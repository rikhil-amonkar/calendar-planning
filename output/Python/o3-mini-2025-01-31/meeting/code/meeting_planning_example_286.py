#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

def time_str_to_minutes(t):
    # t in H:MM format, e.g., "9:00"
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time_str(m):
    # convert minutes to H:MM string (24-hour, no leading zero on hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters and travel times (in minutes)
    travel = {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Sunset District"): 26,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Sunset District"): 23,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Bayview"): 22
    }
    
    # Meeting constraints (all times in minutes from midnight)
    start_location = "Union Square"
    arrival_time = time_str_to_minutes("9:00")
    
    # Friends' availability windows and meeting durations (in minutes)
    # Format: (location, available_start, available_end, min_meeting_duration)
    meetings = {
        "Rebecca": {
            "location": "Mission District",
            "avail_start": time_str_to_minutes("11:30"),
            "avail_end": time_str_to_minutes("20:15"),
            "min_duration": 120
        },
        "Karen": {
            "location": "Bayview",
            "avail_start": time_str_to_minutes("12:45"),
            "avail_end": time_str_to_minutes("15:00"),
            "min_duration": 120
        },
        "Carol": {
            "location": "Sunset District",
            "avail_start": time_str_to_minutes("10:15"),
            "avail_end": time_str_to_minutes("11:45"),
            "min_duration": 30
        }
    }
    
    # We will explore a schedule that meets all constraints.
    # One feasible order is:
    # 1. Go from Union Square to Sunset District to meet Carol.
    # 2. Then travel from Sunset District to Bayview to meet Karen.
    # 3. Then travel from Bayview to Mission District to meet Rebecca.
    itinerary = []

    current_time = arrival_time
    current_location = start_location

    # --- Meeting Carol at Sunset District ---
    # Travel from Union Square to Sunset District
    travel_time = travel[(current_location, meetings["Carol"]["location"])]
    current_time += travel_time
    # If arrived earlier than Carol's available start, wait
    if current_time < meetings["Carol"]["avail_start"]:
        current_time = meetings["Carol"]["avail_start"]
    # Schedule Carol meeting for minimum duration
    carol_meet_start = current_time
    carol_meet_end = carol_meet_start + meetings["Carol"]["min_duration"]
    # Ensure meeting ends before Carol's availability end (should be within window)
    if carol_meet_end > meetings["Carol"]["avail_end"]:
        raise Exception("Cannot meet Carol within her availability window.")
    itinerary.append({
        "action": "meet",
        "location": meetings["Carol"]["location"],
        "person": "Carol",
        "start_time": minutes_to_time_str(carol_meet_start),
        "end_time": minutes_to_time_str(carol_meet_end)
    })
    # Update current time and location after Carol meeting
    current_time = carol_meet_end
    current_location = meetings["Carol"]["location"]

    # --- Meeting Karen at Bayview ---
    # Travel from Sunset District to Bayview
    travel_time = travel[(current_location, meetings["Karen"]["location"])]
    current_time += travel_time
    current_location = meetings["Karen"]["location"]
    # Wait until Karen's availability start if needed
    if current_time < meetings["Karen"]["avail_start"]:
        current_time = meetings["Karen"]["avail_start"]
    # Schedule Karen meeting for minimum duration
    karen_meet_start = current_time
    karen_meet_end = karen_meet_start + meetings["Karen"]["min_duration"]
    if karen_meet_end > meetings["Karen"]["avail_end"]:
        raise Exception("Cannot meet Karen within her availability window.")
    itinerary.append({
        "action": "meet",
        "location": meetings["Karen"]["location"],
        "person": "Karen",
        "start_time": minutes_to_time_str(karen_meet_start),
        "end_time": minutes_to_time_str(karen_meet_end)
    })
    current_time = karen_meet_end
    current_location = meetings["Karen"]["location"]

    # --- Meeting Rebecca at Mission District ---
    # Travel from Bayview to Mission District
    travel_time = travel[(current_location, meetings["Rebecca"]["location"])]
    current_time += travel_time
    current_location = meetings["Rebecca"]["location"]
    # Wait until Rebecca's availability start if needed
    if current_time < meetings["Rebecca"]["avail_start"]:
        current_time = meetings["Rebecca"]["avail_start"]
    # Schedule Rebecca meeting for minimum duration
    rebecca_meet_start = current_time
    rebecca_meet_end = rebecca_meet_start + meetings["Rebecca"]["min_duration"]
    if rebecca_meet_end > meetings["Rebecca"]["avail_end"]:
        raise Exception("Cannot meet Rebecca within her availability window.")
    itinerary.append({
        "action": "meet",
        "location": meetings["Rebecca"]["location"],
        "person": "Rebecca",
        "start_time": minutes_to_time_str(rebecca_meet_start),
        "end_time": minutes_to_time_str(rebecca_meet_end)
    })
    
    # Prepare final result
    schedule = {"itinerary": itinerary}
    # Output the result as JSON formatted dictionary
    print(json.dumps(schedule, indent=2))

if __name__ == "__main__":
    main()