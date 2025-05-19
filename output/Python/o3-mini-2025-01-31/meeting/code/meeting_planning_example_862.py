#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper functions to convert times
def str_to_minutes(time_str):
    # Expects time in "H:MM" 24-hour format, returns minutes from midnight
    parts = time_str.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_str(minutes):
    # Converts minutes from midnight to "H:MM" (no leading zero on hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Set up input parameters
# Starting point and arrival time at Mission District
start_location = "Mission District"
start_time = str_to_minutes("9:00")

# Meeting constraints: each friend has a meeting location, availability (start, end) and minimum meeting duration (in minutes)
friends = {
    "Laura": {"location": "Alamo Square", "avail_start": str_to_minutes("14:30"), "avail_end": str_to_minutes("16:15"), "duration": 75},
    "Brian": {"location": "Presidio", "avail_start": str_to_minutes("10:15"), "avail_end": str_to_minutes("17:00"), "duration": 30},
    "Karen": {"location": "Russian Hill", "avail_start": str_to_minutes("18:00"), "avail_end": str_to_minutes("20:15"), "duration": 90},
    "Stephanie": {"location": "North Beach", "avail_start": str_to_minutes("10:15"), "avail_end": str_to_minutes("16:00"), "duration": 75},
    "Helen": {"location": "Golden Gate Park", "avail_start": str_to_minutes("11:30"), "avail_end": str_to_minutes("21:45"), "duration": 120},
    "Sandra": {"location": "Richmond District", "avail_start": str_to_minutes("8:00"),  "avail_end": str_to_minutes("15:15"), "duration": 30},
    "Mary": {"location": "Embarcadero", "avail_start": str_to_minutes("16:45"), "avail_end": str_to_minutes("18:45"), "duration": 120},
    "Deborah": {"location": "Financial District", "avail_start": str_to_minutes("19:00"), "avail_end": str_to_minutes("20:45"), "duration": 105},
    "Elizabeth": {"location": "Marina District", "avail_start": str_to_minutes("8:30"), "avail_end": str_to_minutes("13:15"), "duration": 105},
}

# Travel times (in minutes) as provided.
# We use a dictionary with keys as (origin, destination)
travel = {
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Marina District"): 19,
    
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Marina District"): 15,
    
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,
    
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Marina District"): 9,
    
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Marina District"): 16,
    
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Marina District"): 9,
    
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,
    
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Marina District"): 15,
    
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
}

# For maximum number of friends, we try to schedule an itinerary that meets 7 of the 9 friends.
# Due to time window conflicts in the afternoon, we choose the following order:
# 1. Elizabeth at Marina District
# 2. Brian at Presidio
# 3. Stephanie at North Beach
# 4. Sandra at Richmond District
# 5. Laura at Alamo Square
# 6. Mary at Embarcadero
# 7. Deborah at Financial District
#
# The algorithm below computes departure and meeting times using travel times and waiting as necessary.

itinerary = []
current_location = start_location
current_time = start_time

def travel_to(destination, curr_loc, curr_time):
    # get travel time from curr_loc to destination. Assumes key exists.
    t = travel.get((curr_loc, destination))
    if t is None:
        # If not found, try reverse (non-symmetric)
        t = travel.get((destination, curr_loc), 0)
    return curr_time + t, t

# 1. Meet Elizabeth at Marina District.
friend = "Elizabeth"
loc = friends[friend]["location"]
# Travel from Mission District to Marina District.
arrival, t_time = travel_to(loc, current_location, current_time)
# Schedule meeting start as max(arrival, friend's available start)
meeting_start = max(arrival, friends[friend]["avail_start"])
# Meeting duration is fixed.
meeting_end = meeting_start + friends[friend]["duration"]
itinerary.append({
    "action": "meet",
    "location": loc,
    "person": friend,
    "start_time": minutes_to_str(meeting_start),
    "end_time": minutes_to_str(meeting_end)
})
current_location = loc
current_time = meeting_end

# 2. Meet Brian at Presidio.
friend = "Brian"
loc = friends[friend]["location"]
arrival, t_time = travel_to(loc, current_location, current_time)
meeting_start = max(arrival, friends[friend]["avail_start"])
meeting_end = meeting_start + friends[friend]["duration"]
itinerary.append({
    "action": "meet",
    "location": loc,
    "person": friend,
    "start_time": minutes_to_str(meeting_start),
    "end_time": minutes_to_str(meeting_end)
})
current_location = loc
current_time = meeting_end

# 3. Meet Stephanie at North Beach.
friend = "Stephanie"
loc = friends[friend]["location"]
arrival, t_time = travel_to(loc, current_location, current_time)
meeting_start = max(arrival, friends[friend]["avail_start"])
meeting_end = meeting_start + friends[friend]["duration"]
itinerary.append({
    "action": "meet",
    "location": loc,
    "person": friend,
    "start_time": minutes_to_str(meeting_start),
    "end_time": minutes_to_str(meeting_end)
})
current_location = loc
current_time = meeting_end

# 4. Meet Sandra at Richmond District.
friend = "Sandra"
loc = friends[friend]["location"]
arrival, t_time = travel_to(loc, current_location, current_time)
meeting_start = max(arrival, friends[friend]["avail_start"])
meeting_end = meeting_start + friends[friend]["duration"]
itinerary.append({
    "action": "meet",
    "location": loc,
    "person": friend,
    "start_time": minutes_to_str(meeting_start),
    "end_time": minutes_to_str(meeting_end)
})
current_location = loc
current_time = meeting_end

# 5. Meet Laura at Alamo Square.
friend = "Laura"
loc = friends[friend]["location"]
arrival, t_time = travel_to(loc, current_location, current_time)
# Might need to wait for Laura's available start.
meeting_start = max(arrival, friends[friend]["avail_start"])
meeting_end = meeting_start + friends[friend]["duration"]
itinerary.append({
    "action": "meet",
    "location": loc,
    "person": friend,
    "start_time": minutes_to_str(meeting_start),
    "end_time": minutes_to_str(meeting_end)
})
current_location = loc
current_time = meeting_end

# 6. Meet Mary at Embarcadero.
friend = "Mary"
loc = friends[friend]["location"]
arrival, t_time = travel_to(loc, current_location, current_time)
# Wait until Mary's availability starts if arrived early.
meeting_start = max(arrival, friends[friend]["avail_start"])
meeting_end = meeting_start + friends[friend]["duration"]
itinerary.append({
    "action": "meet",
    "location": loc,
    "person": friend,
    "start_time": minutes_to_str(meeting_start),
    "end_time": minutes_to_str(meeting_end)
})
current_location = loc
current_time = meeting_end

# 7. Meet Deborah at Financial District.
friend = "Deborah"
loc = friends[friend]["location"]
arrival, t_time = travel_to(loc, current_location, current_time)
meeting_start = max(arrival, friends[friend]["avail_start"])
meeting_end = meeting_start + friends[friend]["duration"]
itinerary.append({
    "action": "meet",
    "location": loc,
    "person": friend,
    "start_time": minutes_to_str(meeting_start),
    "end_time": minutes_to_str(meeting_end)
})
current_location = loc
current_time = meeting_end

# The itinerary is computed based on travel times and waiting times.
# We built a schedule that meets 7 friends out of the available 9.
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))