import json
import os
import sqlite3
import threading
import time
from datetime import datetime
from flask import Flask, request, jsonify
import tkinter as tk
from tkinter import ttk, scrolledtext
import logging
import queue

# --- Flask Server Setup (for GSI) ---
app = Flask(__name__)
# Suppress Flask's default request logging for cleaner console output
log = logging.getLogger('werkzeug')
log.setLevel(logging.WARNING)

# --- Configure a file handler for raw GSI data ---
raw_gsi_logger = logging.getLogger('raw_gsi_data')
raw_gsi_logger.setLevel(logging.INFO)
file_handler = logging.FileHandler('raw_gsi_data.log', mode='a') # 'a' for append mode
formatter = logging.Formatter('%(message)s')
file_handler.setFormatter(formatter)
raw_gsi_logger.addHandler(file_handler)

# --- Configuration ---
DATABASE_FILE = "tracker.db"
AUTH_TOKEN = "my_cs2_tracker_secret" # MUST match the token in your .cfg file!
INITIAL_XP_SCORE = 0 # Starting XP Score for new players

# Your in-game name for display purposes.
# The tracker will ONLY process stats if the player.name from GSI matches this.
MY_PLAYER_NAME = "basilisk" # Your player name for filtering GSI data

# XP Score adjustment parameters - TUNE THESE TO YOUR PREFERENCE
XP_PER_KILL = 150
XP_PER_DEATH = 145
XP_PER_ASSIST_GAIN = 135 # Corrected: XP gained for each assist
XP_BONUS_WIN = 700
XP_PENALTY_LOSS = 650

# Define XP Score ranges for your 1-10 skill levels
# The key is the level, the value is the minimum XP required for that level
XP_LEVELS = {
    1: 0,
    2: 5000,
    3: 12000, # Fixed: Removed duplicate entry for Level 3
    4: 20000,
    5: 30000,
    6: 42000,
    7: 56000,
    8: 72000,
    9: 88000,
    10: 100000
}

# --- Global Match State Variables ---
current_match_id = None
last_processed_round_num = -1
# Stores player stats at the beginning of the *current* round for per-round calculation (for DB)
my_match_stats_at_round_start = {
    "kills": 0, "deaths": 0, "assists": 0,
    "headshot_kills": 0, "damage": 0
}
# Stores player stats from the *last GSI update* for incremental live XP calculation
my_match_stats_at_last_gsi_update = {
    "kills": 0, "deaths": 0, "assists": 0,
    "headshot_kills": 0, "damage": 0
}
is_in_competitive_match = False  # Flag to indicate if we are currently tracking a comp match
current_match_xp_gain = 0  # Accumulate XP throughout the current match
my_team_in_match = "" # Stores the player's team for the current match

# --- Tkinter UI Elements (Globals for easy update) ---
root = None
status_label = None
level_label = None
xp_label = None
average_kd_label = None
xp_progress = None
xp_progress_label = None
console_output = None
current_match_kills_label = None
current_match_deaths_label = None
current_match_assists_label = None
current_match_kd_label = None


# Variables for progress bar calculation
current_level_min_xp = 0
next_level_min_xp = 0

# --- Global Message Queue for Thread-Safe UI Updates ---
message_queue = queue.Queue()

# --- Database Functions ---
def get_db_connection():
    """Establishes and returns a database connection."""
    conn = sqlite3.connect(DATABASE_FILE)
    conn.row_factory = sqlite3.Row  # Allows accessing columns by name
    return conn

def init_db():
    """Initializes the database tables and ensures a player record exists."""
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS players (
                player_id INTEGER PRIMARY KEY CHECK (player_id = 1),
                xp_score INTEGER NOT NULL,
                level INTEGER NOT NULL
            )
        ''')
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS matches (
                match_id TEXT PRIMARY KEY,
                start_time TEXT NOT NULL,
                map_name TEXT,
                game_mode TEXT,
                final_my_kills INTEGER,
                final_my_deaths INTEGER,
                final_my_assists INTEGER,
                final_score_ct INTEGER,
                final_score_t INTEGER,
                win BOOLEAN,
                xp_change INTEGER,
                xp_before INTEGER,
                xp_after INTEGER,
                rounds_data TEXT
            )
        ''')
        conn.commit()
    log_to_console(f"Database '{DATABASE_FILE}' initialized successfully.")
    player_record = get_player()
    if player_record is None:
        # Initialize player with default XP if no record exists
        upsert_player(INITIAL_XP_SCORE, get_skill_level_from_xp(INITIAL_XP_SCORE))
        log_to_console("Initialized new player record with 0 XP.")

def get_player():
    """Retrieves the player's current XP and level from the database."""
    with get_db_connection() as conn:
        player = conn.execute('SELECT * FROM players WHERE player_id = 1').fetchone()
    return player

def upsert_player(xp_score, level):
    """Inserts or updates the player's XP and level in the database."""
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute('''
            INSERT INTO players (player_id, xp_score, level)
            VALUES (1, ?, ?)
            ON CONFLICT(player_id) DO UPDATE SET
                xp_score = EXCLUDED.xp_score,
                level = EXCLUDED.level
        ''', (xp_score, level))
        conn.commit()

# --- XP Score and Level Calculation Functions ---
def calculate_round_xp_change(round_kills, round_deaths, round_assists=0):
    """Calculates XP change for a single round based on kills, deaths, and assists."""
    xp_gained = (round_kills * XP_PER_KILL) + (round_assists * XP_PER_ASSIST_GAIN)
    xp_lost = (round_deaths * XP_PER_DEATH)
    return xp_gained - xp_lost

def get_skill_level_from_xp(xp_score):
    """Determines the skill level based on the current XP score."""
    global current_level_min_xp, next_level_min_xp

    sorted_levels = sorted(XP_LEVELS.items(), key=lambda item: item[1])

    level = 1  # Default to Level 1
    current_level_min_xp = 0  # Default min XP for current level
    next_level_min_xp = sorted_levels[0][1] if len(sorted_levels) > 0 else 0  # Default next level min XP

    for i, (lvl, min_xp) in enumerate(sorted_levels):
        if xp_score >= min_xp:
            level = lvl
            current_level_min_xp = min_xp
            # Determine next level's min XP
            if i + 1 < len(sorted_levels):
                next_level_min_xp = sorted_levels[i+1][1]
            else:
                # If at max level, set next_level_min_xp far beyond current to show 100% progress
                next_level_min_xp = XP_LEVELS[10] * 2
        else:
            # We've passed the current level range
            if i > 0 and xp_score < min_xp: # Found the level range
                current_level_min_xp = sorted_levels[i-1][1]
                next_level_min_xp = min_xp
                break # Found our level, stop iterating
            elif i == 0 and xp_score < min_xp: # Below first level
                current_level_min_xp = 0
                next_level_min_xp = sorted_levels[0][1]
                break
    return level

# --- GSI Data Handler ---
@app.route('/gsi', methods=['POST'])
def gsi_data_handler():
    """Receives and processes Game State Integration data from CS2."""
    global current_match_id, last_processed_round_num, my_match_stats_at_round_start
    global is_in_competitive_match, current_match_xp_gain, my_match_stats_at_last_gsi_update
    global my_team_in_match # Access the global team variable

    data = request.json

    # --- Log all raw incoming GSI data to file for debugging ---
    if data:
        raw_gsi_logger.info(json.dumps(data, indent=2))
    else:
        log_to_console("Received empty data payload from GSI.")
        return jsonify({"status": "error", "message": "No data received"}), 400

    # --- Authentication Check ---
    auth_data = data.get('auth', {})
    if auth_data.get('token') != AUTH_TOKEN:
        log_to_console(f"Authentication failed: Invalid token '{auth_data.get('token')}'")
        return jsonify({"status": "error", "message": "Unauthorized"}), 401

    # Extract relevant GSI data
    my_player_name_from_gsi = data.get('player', {}).get('name')
    my_player_activity = data.get('player', {}).get('activity')
    game_mode = data.get('map', {}).get('mode')
    game_phase = data.get('map', {}).get('phase')
    map_data = data.get('map', {})
    round_data = data.get('round', {})
    my_player_info_general = data.get('player_state', {})
    current_gsi_player_team = my_player_info_general.get('team', '').lower() # Get current team from GSI

    # Get my_current_match_stats from the 'player' block.
    my_current_match_stats = data.get('player', {}).get('match_stats', {})
    if not my_current_match_stats:
        my_current_match_stats = { "kills": 0, "deaths": 0, "assists": 0, "headshot_kills": 0, "damage": 0 }
        log_to_console("WARNING: 'player.match_stats' missing in GSI data. Using default 0s.")

    # --- NEW: Logic to update my_team_in_match consistently ---
    # This ensures the team is correctly updated after side switches or if it was initially empty.
    # The list of tracked game modes is now expanded to include 'casual'
    is_my_player_active_and_in_comp = (
        my_player_name_from_gsi == MY_PLAYER_NAME and
        my_player_activity in ["playing", "textinput"] and
        game_mode in ["competitive", "scrimcomp", "premier", "casual"] and
        game_phase == "live"
    )

    if is_my_player_active_and_in_comp and current_gsi_player_team and my_team_in_match != current_gsi_player_team:
        log_to_console(f"Updating stored player team from '{my_team_in_match}' to '{current_gsi_player_team}'.")
        my_team_in_match = current_gsi_player_team
    elif is_my_player_active_and_in_comp and current_gsi_player_team and not my_team_in_match:
        log_to_console(f"Setting initial stored player team to: '{current_gsi_player_team}'.")
        my_team_in_match = current_gsi_player_team


    log_to_console(f"\n--- GSI Update ({datetime.now().strftime('%H:%M:%S')}) ---")
    log_to_console(f"Player Name from GSI: {my_player_name_from_gsi}, Activity: {my_player_activity}")
    log_to_console(f"Game Mode: {game_mode}, Phase: {game_phase}, Round Phase: {round_data.get('phase')}")
    log_to_console(f"Current Round Num: {round_data.get('round_num', -1)}, Last Processed Round: {last_processed_round_num}")
    log_to_console(f"is_in_competitive_match (before processing): {is_in_competitive_match}")
    log_to_console(f"My cumulative K/D/A (from GSI): {my_current_match_stats.get('kills',0)}/{my_current_match_stats.get('deaths',0)}/{my_current_match_stats.get('assists',0)}")
    log_to_console(f"Current GSI Player Team: '{current_gsi_player_team}', Stored Team: '{my_team_in_match}'")


    # --- Match Finalization Logic (Highest Priority) ---
    # This block handles the definitive end of a match.
    if is_in_competitive_match and game_phase == "gameover":
        log_to_console(f"\n--- COMPETITIVE/CASUAL Match Ended (Game Over): {current_match_id} ---")
        # Finalize using the last known stats for MY_PLAYER_NAME and the stored team
        finalize_and_save_match_data(map_data, my_match_stats_at_last_gsi_update, my_team_in_match) # Use stored team

        # Reset state for the next match
        current_match_id = None
        last_processed_round_num = -1
        my_match_stats_at_round_start = { "kills": 0, "deaths": 0, "assists": 0, "headshot_kills": 0, "damage": 0 }
        my_match_stats_at_last_gsi_update = { "kills": 0, "deaths": 0, "assists": 0, "headshot_kills": 0, "damage": 0 }
        is_in_competitive_match = False
        current_match_xp_gain = 0
        my_team_in_match = "" # Reset stored team for next match
        log_to_console("Match state reset for new game.")
        return jsonify({"status": "success", "message": "Match ended, data finalized."})

    # --- Handle Player Leaving/Spectating/Bot Takeover (If currently tracking but no longer active) ---
    # This pauses live XP updates but does NOT finalize the match unless it's truly gameover.
    if is_in_competitive_match and not is_my_player_active_and_in_comp:
        log_to_console(f"Player '{MY_PLAYER_NAME}' not active in live competitive/casual game. Pausing live updates for current match.")
        # Do NOT finalize here, just stop processing live updates.
        return jsonify({"status": "success", "message": "Player not active, pausing live updates."})


    # --- Match Start Logic (If not currently tracking and MY_PLAYER_NAME is active) ---
    if not is_in_competitive_match and is_my_player_active_and_in_comp:
        is_in_competitive_match = True
        current_match_id = f"match_{game_mode}_{datetime.now().strftime('%Y%m%d_%H%M%S')}" # Modified match ID for casual and comp

        # Initialize / Reset match stats for new match using current GSI data for MY_PLAYER_NAME
        my_match_stats_at_round_start = {
            "kills": my_current_match_stats.get('kills', 0),
            "deaths": my_current_match_stats.get('deaths', 0),
            "assists": my_current_match_stats.get('assists', 0),
            "headshot_kills": my_current_match_stats.get('headshot_kills', 0),
            "damage": my_current_match_stats.get('damage', 0)
        }
        my_match_stats_at_last_gsi_update = dict(my_match_stats_at_round_start) # Copy initial stats
        last_processed_round_num = -1
        current_match_xp_gain = 0
        # my_team_in_match is already handled by the new logic block above this.

        with get_db_connection() as conn:
            conn.execute('''
                INSERT INTO matches (match_id, start_time, map_name, game_mode, rounds_data)
                VALUES (?, ?, ?, ?, ?)
            ''', (current_match_id, datetime.now().isoformat(),
                  map_data.get('name'), game_mode, json.dumps([])))
            conn.commit()

        log_to_console(f"\n--- New COMPETITIVE/CASUAL Match Started: {map_data.get('name')} ({game_mode}) ---")
        log_to_console(f"Tracking Match ID: {current_match_id}")
        log_to_console(f"Stored Player Team for Match: '{my_team_in_match}'") # Log stored team
        player_record = get_player()
        log_to_console(f"Your current XP Score at match start: {player_record['xp_score']}, Level: {player_record['level']}")
        log_to_console(f"DEBUG START: Initial my_match_stats_at_round_start: {my_match_stats_at_round_start}")
        log_to_console(f"DEBUG START: Initial my_match_stats_at_last_gsi_update: {my_match_stats_at_last_gsi_update}")

    # --- Skip processing if not in a tracked game mode and MY_PLAYER_NAME is not active ---
    elif not is_in_competitive_match and not is_my_player_active_and_in_comp:
        log_to_console(f"Not playing as {MY_PLAYER_NAME} in a tracked competitive/casual match or not in a live phase. Skipping stat processing.")
        return jsonify({"status": "success", "message": "Not playing as specified player or not competitive/casual, skipped processing."})


    # --- Process Live Game Data for XP (This block ONLY executes if is_in_competitive_match is True AND is_my_player_active_and_in_comp is True) ---
    current_kills = my_current_match_stats.get('kills', 0)
    current_deaths = my_current_match_stats.get('deaths', 0)
    current_assists = my_current_match_stats.get('assists', 0)

    # Calculate kills/deaths/assists since the LAST GSI update
    kills_since_last_gsi = max(0, current_kills - my_match_stats_at_last_gsi_update['kills'])
    deaths_since_last_gsi = max(0, current_deaths - my_match_stats_at_last_gsi_update['deaths'])
    assists_since_last_gsi = max(0, current_assists - my_match_stats_at_last_gsi_update['assists'])

    if kills_since_last_gsi > 0 or deaths_since_last_gsi > 0 or assists_since_last_gsi > 0:
        xp_from_this_gsi_update = calculate_round_xp_change(kills_since_last_gsi, deaths_since_last_gsi, assists_since_last_gsi)
        current_match_xp_gain += xp_from_this_gsi_update
        log_to_console(f"LIVE XP Update (KDA): Kills: {kills_since_last_gsi}, Deaths: {deaths_since_last_gsi}, Assists: {assists_since_last_gsi}, XP Change: {xp_from_this_gsi_update}, Total Match XP: {current_match_xp_gain}")

    # Update my_match_stats_at_last_gsi_update for the next GSI tick
    my_match_stats_at_last_gsi_update = {
        "kills": current_kills,
        "deaths": current_deaths,
        "assists": current_assists,
        "headshot_kills": my_current_match_stats.get('headshot_kills', 0),
        "damage": my_current_match_stats.get('damage', 0)
    }

    # --- Process Round End Data (for saving round summary to DB) ---
    current_round_num = round_data.get('round_num', -1)
    round_phase = round_data.get('phase')

    if is_in_competitive_match and current_round_num != -1 and \
       current_round_num > last_processed_round_num and \
       (round_phase == 'over' or round_phase == 'freezetime' or game_phase == 'intermission'):

        log_to_console(f"\n--- Processing Round {current_round_num} (for DB save) ---")
        log_to_console(f"Round Phase: '{round_phase}', Game Phase: '{game_phase}'")
        log_to_console(f"Previous Round Num: {last_processed_round_num}")

        # Calculate kills/deaths/assists for THIS ROUND only (using stats from round start)
        round_kills = max(0, my_current_match_stats.get('kills', 0) - my_match_stats_at_round_start['kills'])
        round_deaths = max(0, my_current_match_stats.get('deaths', 0) - my_match_stats_at_round_start['deaths'])
        round_assists = max(0, my_current_match_stats.get('assists', 0) - my_match_stats_at_round_start['assists'])

        xp_change_for_db_round = calculate_round_xp_change(round_kills, round_deaths, round_assists)

        round_kd = round_kills / (round_deaths if round_deaths > 0 else 1)

        # Retrieve existing round data for the current match
        rounds_list = []
        with get_db_connection() as conn:
            match_record = conn.execute('SELECT rounds_data FROM matches WHERE match_id = ?', (current_match_id,)).fetchone()
            if match_record and match_record['rounds_data']:
                rounds_list = json.loads(match_record['rounds_data'])

        round_info = {
            "round_num": current_round_num,
            "win_team": round_data.get('win_team'),
            "round_ends_reason": round_data.get('end_reason'),
            "my_round_stats": {
                "kills": round_kills,
                "deaths": round_deaths,
                "assists": round_assists,
                "k_d": round_kd,
                "xp_change": xp_change_for_db_round
            },
            "my_cumulative_match_stats": {
                "kills": my_current_match_stats.get('kills', 0),
                "deaths": my_current_match_stats.get('deaths', 0),
                "assists": my_current_match_stats.get('assists', 0),
                "k_d": my_current_match_stats.get('kills', 0) / (my_current_match_stats.get('deaths', 0) if my_current_match_stats.get('deaths', 0) > 0 else 1),
                "total_match_xp_so_far": current_match_xp_gain
            }
        }
        rounds_list.append(round_info)

        # Update the matches table with the new round data
        with get_db_connection() as conn:
            conn.execute('UPDATE matches SET rounds_data = ? WHERE match_id = ?', (json.dumps(rounds_list), current_match_id))
            conn.commit()

        log_to_console(f"  Round {current_round_num} DB Save - K: {round_kills}, D: {round_deaths}, A: {round_assists}, K/D: {round_kd:.2f}, XP (Round): {xp_change_for_db_round}")
        log_to_console(f"  Match K/D so far: {my_current_match_stats.get('kills', 0) / (my_current_match_stats.get('deaths', 0) if my_current_match_stats.get('deaths', 0) > 0 else 1):.2f}, Total Match XP (current match): {current_match_xp_gain}")
        log_to_console(f"  LAST_PROCESSED_ROUND_NUM updated to: {current_round_num}")

        # IMPORTANT: Update my_match_stats_at_round_start for the *next* round's calculation
        my_match_stats_at_round_start = {
            "kills": my_current_match_stats.get('kills', 0),
            "deaths": my_current_match_stats.get('deaths', 0),
            "assists": my_current_match_stats.get('assists', 0),
            "headshot_kills": my_current_match_stats.get('headshot_kills', 0),
            "damage": my_current_match_stats.get('damage', 0)
        }
        last_processed_round_num = current_round_num

    return jsonify({"status": "success"})


def finalize_and_save_match_data(map_data, final_my_stats, my_player_team_stored): # Renamed for clarity
    """Calculates final match XP and saves match summary to the database."""
    global current_match_id, current_match_xp_gain

    if not current_match_id:
        log_to_console("Error: No active match ID to finalize.")
        return

    final_my_kills = final_my_stats.get('kills', 0)
    final_my_deaths = final_my_stats.get('deaths', 0)
    final_my_assists = final_my_stats.get('assists', 0)

    log_to_console(f"\n--- ATTEMPTING MATCH FINALIZATION: {current_match_id} ---")
    log_to_console(f"Player's Final K/D/A: K:{final_my_kills}, D:{final_my_deaths}, A:{final_my_assists}")

    final_score_ct = map_data.get('team_ct', {}).get('score', 0)
    final_score_t = map_data.get('team_t', {}).get('score', 0)
    # Log the exact scores and *stored* player team used for decision
    log_to_console(f"DEBUG FINALIZATION: GSI CT Score: {final_score_ct}, T Score: {final_score_t}, Stored Player Team: '{my_player_team_stored}'")


    win_status = None  # Default to Draw
    if my_player_team_stored == 'ct' and final_score_ct > final_score_t:
        win_status = True
        current_match_xp_gain += XP_BONUS_WIN
        log_to_console(f"MATCH END: Applied WIN bonus XP: +{XP_BONUS_WIN}. Reason: My stored team (CT) had higher score.")
    elif my_player_team_stored == 't' and final_score_t > final_score_ct:
        win_status = True
        current_match_xp_gain += XP_BONUS_WIN
        log_to_console(f"MATCH END: Applied WIN bonus XP: +{XP_BONUS_WIN}. Reason: My stored team (T) had higher score.")
    elif final_score_ct == final_score_t:  # Consider a draw if scores are equal
        win_status = None
        log_to_console("MATCH END: Match was a DRAW. No win/loss XP applied (scores were equal).")
    else:
        win_status = False
        current_match_xp_gain -= XP_PENALTY_LOSS
        log_to_console(f"MATCH END: Applied LOSS penalty XP: -{XP_PENALTY_LOSS}. Reason: My stored team did not have higher score or scores were not equal.")

    player_record = get_player()
    xp_before_match = player_record['xp_score'] if player_record else INITIAL_XP_SCORE

    xp_after_match = xp_before_match + current_match_xp_gain

    if xp_after_match < 0:  # Prevent XP from going below zero
        xp_after_match = 0

    new_skill_level = get_skill_level_from_xp(xp_after_match)

    with get_db_connection() as conn:
        conn.execute('''
            UPDATE players SET
                xp_score = ?,
                level = ?
            WHERE player_id = 1
        ''', (xp_after_match, new_skill_level))
        conn.execute('''
            UPDATE matches SET
                final_my_kills = ?, final_my_deaths = ?, final_my_assists = ?,
                final_score_ct = ?, final_score_t = ?, win = ?,
                xp_change = ?, xp_before = ?, xp_after = ?
            WHERE match_id = ?
        ''', (
            final_my_kills,
            final_my_deaths,
            final_my_assists,
            final_score_ct,
            final_score_t,
            win_status,
            current_match_xp_gain,
            xp_before_match,
            xp_after_match,
            current_match_id
        ))
        conn.commit()

    # Removed redundant upsert_player call here as the UPDATE players query handles it.
    # upsert_player(xp_after_match, new_skill_level)

    log_to_console(f"Match {current_match_id} finalized and saved.")
    log_to_console(f"Final XP Change: {current_match_xp_gain} | XP Before: {xp_before_match} | XP After: {xp_after_match} | New Level: {new_skill_level}")
    log_to_console("---------------------------------------")


# --- Flask Server Thread ---
def run_flask_server():
    """Initializes the database and starts the Flask web server."""
    init_db()
    log_to_console(f"Listening for CS2 GSI data on http://127.0.0.1:5000/gsi")
    log_to_console("Your competitive/casual match stats will appear here as you play.")
    try:
        # use_reloader=False is crucial when running Flask in a separate thread
        app.run(host='127.0.0.1', port=5000, debug=False, use_reloader=False)
    except Exception as e:
        log_to_console(f"Flask server error: {e}")

# --- Tkinter UI Functions ---
def log_to_console(message):
    """Thread-safe way to add messages to the Tkinter console output."""
    message_queue.put(message)

def process_queue_messages():
    """Reads messages from the queue and updates the console output."""
    while not message_queue.empty():
        try:
            message = message_queue.get_nowait()
            if console_output:  # Ensure widget exists before inserting
                console_output.insert(tk.END, message + "\n")
                console_output.see(tk.END)  # Auto-scroll to the end
        except queue.Empty:
            pass  # No more messages
    # Schedule itself to run again after a short delay (e.g., 100ms)
    root.after(100, process_queue_messages)

def update_ui_stats():
    """Updates the main UI stats (Level, XP, K/D, Status)."""
    global current_level_min_xp, next_level_min_xp
    global current_match_kills_label, current_match_deaths_label, current_match_assists_label, current_match_kd_label

    player_record = get_player()
    base_xp_from_db = player_record['xp_score'] if player_record else INITIAL_XP_SCORE

    displayed_xp = base_xp_from_db
    # Only add current match XP if we are actively playing a match
    if is_in_competitive_match:
        displayed_xp += current_match_xp_gain

    current_level = get_skill_level_from_xp(displayed_xp)

    status_label.config(text=f"Status: {'Tracking Match' if is_in_competitive_match else 'Waiting for Competitive/Casual Match'}")
    level_label.config(text=f"Level: {current_level}")
    xp_label.config(text=f"XP: {displayed_xp}")

    # --- Update Live Match K/D/A ---
    if is_in_competitive_match: # Only update if we are actively playing a match
        current_match_kills = my_match_stats_at_last_gsi_update.get('kills', 0)
        current_match_deaths = my_match_stats_at_last_gsi_update.get('deaths', 0)
        current_match_assists = my_match_stats_at_last_gsi_update.get('assists', 0)
        current_match_kd = current_match_kills / (current_match_deaths if current_match_deaths > 0 else 1)

        current_match_kills_label.config(text=f"Match Kills: {current_match_kills}")
        current_match_deaths_label.config(text=f"Match Deaths: {current_match_deaths}")
        current_match_assists_label.config(text=f"Match Assists: {current_match_assists}")
        current_match_kd_label.config(text=f"Match K/D: {current_match_kd:.2f}")

    else: # Reset K/D/A labels if not in a match
        current_match_kills_label.config(text="Match Kills: --")
        current_match_deaths_label.config(text="Match Deaths: --")
        current_match_assists_label.config(text="Match Assists: --")
        current_match_kd_label.config(text="Match K/D: --")


    # Calculate overall K/D from historical data
    total_kills = 0
    total_deaths = 0
    with get_db_connection() as conn:
        matches = conn.execute('SELECT final_my_kills, final_my_deaths FROM matches').fetchall()
        for match in matches:
            if match['final_my_kills'] is not None:
                total_kills += match['final_my_kills']
            if match['final_my_deaths'] is not None:
                total_deaths += match['final_my_deaths']

    overall_kd = total_kills / (total_deaths if total_deaths > 0 else 1)
    average_kd_label.config(text=f"Overall K/D: {overall_kd:.2f}")

    # Update XP Progress Bar
    if current_level < 10:
        next_level_xp_needed = 0
        found_current_level = False
        for lvl, min_xp in sorted(XP_LEVELS.items(), key=lambda item: item[0]):
            if lvl == current_level:
                current_level_min_xp = min_xp
                found_current_level = True
            elif found_current_level and lvl == current_level + 1:
                next_level_xp_needed = min_xp
                break
            elif found_current_level and lvl > current_level + 1:
                next_level_xp_needed = min_xp
                break

        progress_range = next_level_xp_needed - current_level_min_xp
        if progress_range > 0:
            current_progress = displayed_xp - current_level_min_xp
            xp_progress['value'] = (current_progress / progress_range) * 100
            xp_progress_label.config(text=f"{current_progress} / {progress_range} XP to Level {current_level + 1}")
        else:
            xp_progress['value'] = 0
            xp_progress_label.config(text="0 / 0 XP (Adjust XP levels or max level)")
    else:
        xp_progress['value'] = 100
        xp_progress_label.config(text="MAX LEVEL!")

    root.after(1000, update_ui_stats)

def on_closing():
    """Handles proper shutdown of the application."""
    log_to_console("Closing tracker. Displaying final overall stats...")
    display_overall_stats()
    root.destroy()
    os._exit(0)

def display_overall_stats():
    """Logs overall player and match statistics to the console."""
    log_to_console("\n--- Overall Tracker Stats for You ---")

    player = get_player()
    if not player:
        log_to_console("No player data found. Play some competitive/casual matches to start tracking!")
        return

    log_to_console(f"Current XP Score: {player['xp_score']}")
    log_to_console(f"Current Skill Level: {player['level']}")

    with get_db_connection() as conn:
        matches = conn.execute('SELECT * FROM matches').fetchall()
        total_matches = len(matches)
        if total_matches == 0:
            log_to_console("No competitive/casual match data tracked yet.")
            return

        wins = sum(1 for m in matches if m['win'] is True)
        losses = sum(1 for m in matches if m['win'] is False)
        draws = sum(1 for m in matches if m['win'] is None)

        total_kills = sum(m['final_my_kills'] for m in matches if m['final_my_kills'] is not None)
        total_deaths = sum(m['final_my_deaths'] for m in matches if m['final_my_deaths'] is not None)
        total_xp_gained_overall = sum(m['xp_change'] for m in matches if m['xp_change'] is not None)

        win_rate = (wins / total_matches) * 100 if total_matches > 0 else 0
        overall_kd = total_kills / (total_deaths if total_deaths > 0 else 1)

        log_to_console(f"Total Competitive/Casual Matches Tracked: {total_matches}")
        log_to_console(f"Wins: {wins}, Losses: {losses}, Draws: {draws}")
        log_to_console(f"Win Rate: {win_rate:.2f}%")
        log_to_console(f"Overall K/D: {overall_kd:.2f}")
        log_to_console(f"Total XP Change Across Matches: {total_xp_gained_overall}")

    log_to_console("----------------------------")

def setup_ui():
    """Sets up the main Tkinter graphical user interface."""
    global root, status_label, level_label, xp_label, average_kd_label, xp_progress, xp_progress_label, console_output
    global current_match_kills_label, current_match_deaths_label, current_match_assists_label, current_match_kd_label

    root = tk.Tk()
    root.title("CS2 Match Stats Tracker - Yousef's App")
    root.geometry("600x650") # Standard window size

    # Ensure UI closes properly even with background threads
    root.protocol("WM_DELETE_WINDOW", on_closing)

    # Main frame for padding
    main_frame = ttk.Frame(root, padding="10")
    main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))

    # Configure the main_frame's grid itself to allow children to expand
    main_frame.columnconfigure(0, weight=1)
    main_frame.rowconfigure(2, weight=1) # Make the row containing the console log expandable

    # Configure the root window's grid to allow main_frame to expand
    root.columnconfigure(0, weight=1)
    root.rowconfigure(0, weight=1) # Allow main frame to expand

    # Status Label
    status_label = ttk.Label(main_frame, text="Status: Initializing...", font=("Segoe UI", 12, "italic"))
    status_label.grid(row=0, column=0, columnspan=2, pady=5, sticky=tk.W)

    # Player Stats Frame
    stats_frame = ttk.LabelFrame(main_frame, text=f"{MY_PLAYER_NAME}'s Current Stats", padding="10")
    stats_frame.grid(row=1, column=0, columnspan=2, padx=5, pady=5, sticky=(tk.W, tk.E))
    stats_frame.columnconfigure(0, weight=1) # Allow stats frame's internal content to expand

    level_label = ttk.Label(stats_frame, text="Level: --", font=("Segoe UI", 18, "bold"))
    level_label.grid(row=0, column=0, sticky=tk.W, pady=2)

    xp_label = ttk.Label(stats_frame, text="XP: --", font=("Segoe UI", 14))
    xp_label.grid(row=1, column=0, sticky=tk.W, pady=2)

    # XP Progress Bar
    xp_progress_label = ttk.Label(stats_frame, text="XP to next level: --", font=("Segoe UI", 10))
    xp_progress_label.grid(row=2, column=0, sticky=tk.W, pady=2)

    xp_progress = ttk.Progressbar(stats_frame, orient="horizontal", length=350, mode="determinate")
    xp_progress.grid(row=3, column=0, sticky=(tk.W, tk.E), pady=5)


    average_kd_label = ttk.Label(stats_frame, text="Overall K/D: --", font=("Segoe UI", 12))
    average_kd_label.grid(row=4, column=0, sticky=tk.W, pady=2)

    # Labels for current match K/D/A
    current_match_kills_label = ttk.Label(stats_frame, text="Match Kills: --", font=("Segoe UI", 12))
    current_match_kills_label.grid(row=5, column=0, sticky=tk.W, pady=2)

    current_match_deaths_label = ttk.Label(stats_frame, text="Match Deaths: --", font=("Segoe UI", 12))
    current_match_deaths_label.grid(row=6, column=0, sticky=tk.W, pady=2)

    current_match_assists_label = ttk.Label(stats_frame, text="Match Assists: --", font=("Segoe UI", 12))
    current_match_assists_label.grid(row=7, column=0, sticky=tk.W, pady=2)

    current_match_kd_label = ttk.Label(stats_frame, text="Match K/D: --", font=("Segoe UI", 12, "bold"))
    current_match_kd_label.grid(row=8, column=0, sticky=tk.W, pady=2)


    # Live Log / Debug Output Frame
    log_frame = ttk.LabelFrame(main_frame, text="Live Game Events & Log", padding="10")
    log_frame.grid(row=2, column=0, columnspan=2, padx=5, pady=5, sticky=(tk.W, tk.E, tk.N, tk.S))
    log_frame.columnconfigure(0, weight=1)
    log_frame.rowconfigure(0, weight=1)

    console_output = scrolledtext.ScrolledText(log_frame, wrap=tk.WORD, width=60, height=15, font=("Consolas", 9),
                                               bg="#282c34", fg="#abb2bf", insertbackground="#ffffff") # Dark theme
    console_output.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))

    # Initial UI Update - this will also kick off the recurring updates
    update_ui_stats()

    # Start processing messages from the queue for console output (important for thread safety)
    root.after(100, process_queue_messages)

    root.mainloop()

# --- Main Execution ---
if __name__ == '__main__':
    # Start the Flask server in a separate daemon thread
    # daemon=True means the thread will automatically exit when the main program exits
    flask_thread = threading.Thread(target=run_flask_server, daemon=True)
    flask_thread.start()

    # Setup and run the Tkinter UI in the main thread
    setup_ui()