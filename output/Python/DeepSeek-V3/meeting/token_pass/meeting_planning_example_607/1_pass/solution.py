import json
import itertools
from datetime import datetime, timedelta

def parse_time(timestr):
    """Convert 'H:MM' or 'HH:MM' string to minutes since midnight."""
    if isinstance(timestr, str):
        h, m = map(int, timestr.split(':'))
        return h * 60 + m
    return timestr

def format_time(minutes):
    """Convert minutes since midnight to 'H:MM' or 'HH:MM'."""
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes: from -> to -> minutes
travel = {
    "Sunset District": {
        "Russian Hill": 24,
        "The Castro": 17,
        "Richmond District": 12,
        "Marina District": 21,
        "North Beach": 29,
        "Union Square": 30,
        "Golden Gate Park": 11,
    },
    "Russian Hill": {
        "Sunset District": 23,
        "The Castro": 21,
        "Richmond District": 14,
        "Marina District": 7,
        "North Beach": 5,
        "Union Square": 11,
        "Golden Gate Park": 21,
    },
    "The Castro": {
        "Sunset District": 17,
        "Russian Hill": 18,
        "Richmond District": 16,
        "Marina District": 21,
        "North Beach": 20,
        "Union Square": 19,
        "Golden Gate Park": 11,
    },
    "Richmond District": {
        "Sunset District": 11,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "North Beach": 17,
        "Union Square": 21,
        "Golden Gate Park": 9,
    },
    "Marina District": {
        "Sunset District": 19,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "North Beach": 11,
        "Union Square": 16,
        "Golden Gate Park": 18,
    },
    "North Beach": {
        "Sunset District": 27,
        "Russian Hill": 4,
        "The Castro": 22,
        "Richmond District": 18,
        "Marina District": 9,
        "Union Square": 7,
        "Golden Gate Park": 22,
    },
    "Union Square": {
        "Sunset District": 26,
        "Russian Hill": 13,
        "The Castro": 19,
        "Richmond District": 20,
        "Marina District": 18,
        "North Beach": 10,
        "Golden Gate Park": 22,
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Russian Hill": 19,
        "The Castro": 13,
        "Richmond District": 7,
        "Marina District": 16,
        "North Beach": 24,
        "Union Square": 22,
    },
}

# Friend data: name, location, window_start, window_end, min_duration (minutes)
friends = [
    ("Karen", "Russian Hill", "20:45", "21:45", 60),
    ("Jessica", "The Castro", "15:45", "19:30", 60),
    ("Matthew", "Richmond District", "7:30", "15:15", 15),
    ("Michelle", "Marina District", "10:30", "18:45", 75),
    ("Carol", "North Beach", "12:00", "17:00", 90),
    ("Stephanie", "Union Square", "10:45", "14:15", 30),
    ("Linda", "Golden Gate Park", "10:45", "22:00", 90),
]

# Convert times to minutes
friends_data = []
for name, loc, start, end, dur in friends:
    friends_data.append({
        "name": name,
        "location": loc,
        "start": parse_time(start),
        "end": parse_time(end),
        "min_dur": dur,
    })

# Start at Sunset District at 9:00
start_time = parse_time("9:00")
start_loc = "Sunset District"

def simulate_order(order):
    """Simulate visiting friends in given order, return (met_count, itinerary)"""
    current_time = start_time
    current_loc = start_loc
    met_count = 0
    itinerary = []
    
    for friend in order:
        # Travel to friend's location
        travel_time = travel[current_loc][friend["location"]]
        arrival = current_time + travel_time
        
        # If we arrive before window start, wait
        if arrival < friend["start"]:
            arrival = friend["start"]
        
        # If we arrive after window end, cannot meet
        if arrival > friend["end"]:
            # Skip this friend in this permutation
            continue
        
        # Check if we can meet minimum duration
        if arrival + friend["min_dur"] > friend["end"]:
            continue
        
        # We can meet
        meet_start = arrival
        meet_end = arrival + friend["min_dur"]
        
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": format_time(meet_start),
            "end_time": format_time(meet_end),
        })
        
        met_count += 1
        current_time = meet_end
        current_loc = friend["location"]
    
    return met_count, itinerary

# Try all permutations to maximize met_count
best_met = 0
best_itinerary = []
best_order = None

# We know one working order from manual check:
manual_order = [
    friends_data[2],  # Matthew
    friends_data[6],  # Linda
    friends_data[5],  # Stephanie
    friends_data[4],  # Carol
    friends_data[3],  # Michelle
    friends_data[1],  # Jessica
    friends_data[0],  # Karen
]

met, itinerary = simulate_order(manual_order)
if met == 7:
    # Found a full schedule
    best_met = met
    best_itinerary = itinerary
else:
    # Fallback: search all permutations (combinatorial but small n=7)
    for perm in itertools.permutations(friends_data):
        met, itinerary = simulate_order(perm)
        if met > best_met:
            best_met = met
            best_itinerary = itinerary
            if best_met == 7:
                break

# Output result
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))