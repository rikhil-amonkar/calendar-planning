import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert '9:00' or '21:30' to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' or 'HH:MM' without leading zero on hour."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times dictionary: travel[from_location][to_location] = minutes
travel = {
    "Pacific Heights": {
        "Marina District": 6,
        "The Castro": 16,
        "Richmond District": 12,
        "Alamo Square": 10,
        "Financial District": 13,
        "Presidio": 11,
        "Mission District": 15,
        "Nob Hill": 8,
        "Russian Hill": 7
    },
    "Marina District": {
        "Pacific Heights": 7,
        "The Castro": 22,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Presidio": 10,
        "Mission District": 20,
        "Nob Hill": 12,
        "Russian Hill": 8
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Marina District": 21,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Presidio": 20,
        "Mission District": 7,
        "Nob Hill": 16,
        "Russian Hill": 18
    },
    "Richmond District": {
        "Pacific Heights": 10,
        "Marina District": 9,
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Presidio": 7,
        "Mission District": 20,
        "Nob Hill": 17,
        "Russian Hill": 13
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Marina District": 15,
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Presidio": 17,
        "Mission District": 10,
        "Nob Hill": 11,
        "Russian Hill": 13
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Marina District": 15,
        "The Castro": 20,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Presidio": 22,
        "Mission District": 17,
        "Nob Hill": 8,
        "Russian Hill": 11
    },
    "Presidio": {
        "Pacific Heights": 11,
        "Marina District": 11,
        "The Castro": 21,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Mission District": 26,
        "Nob Hill": 18,
        "Russian Hill": 14
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Marina District": 19,
        "The Castro": 7,
        "Richmond District": 20,
        "Alamo Square": 11,
        "Financial District": 15,
        "Presidio": 25,
        "Nob Hill": 12,
        "Russian Hill": 15
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Marina District": 11,
        "The Castro": 17,
        "Richmond District": 14,
        "Alamo Square": 11,
        "Financial District": 9,
        "Presidio": 17,
        "Mission District": 13,
        "Russian Hill": 5
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Marina District": 7,
        "The Castro": 21,
        "Richmond District": 14,
        "Alamo Square": 15,
        "Financial District": 11,
        "Presidio": 14,
        "Mission District": 16,
        "Nob Hill": 5
    }
}

# Friends data: name -> (location, window_start, window_end, min_duration_minutes)
friends = {
    "Linda": ("Marina District", "18:00", "22:00", 30),
    "Kenneth": ("The Castro", "14:45", "16:15", 30),
    "Kimberly": ("Richmond District", "14:15", "22:00", 30),
    "Paul": ("Alamo Square", "21:00", "21:30", 15),
    "Carol": ("Financial District", "10:15", "12:00", 60),
    "Brian": ("Presidio", "10:00", "21:30", 75),
    "Laura": ("Mission District", "16:15", "20:30", 30),
    "Sandra": ("Nob Hill", "9:15", "18:30", 60),
    "Karen": ("Russian Hill", "18:30", "22:00", 75)
}

# Convert friends data to minutes
friends_min = {}
for name, (loc, start, end, dur) in friends.items():
    friends_min[name] = (loc, time_to_minutes(start), time_to_minutes(end), dur)

# Start at Pacific Heights at 9:00 AM
start_time = time_to_minutes("9:00")
start_loc = "Pacific Heights"

# Try all permutations of friends
best_count = 0
best_meetings = []
best_total_duration = 0

for perm in itertools.permutations(friends_min.keys()):
    current_time = start_time
    current_loc = start_loc
    meetings = []
    count = 0
    total_duration = 0
    
    for name in perm:
        loc, w_start, w_end, min_dur = friends_min[name]
        # Travel to friend's location
        travel_time = travel[current_loc][loc]
        arrival = current_time + travel_time
        
        # If arrival after window end, cannot meet
        if arrival > w_end:
            continue
        
        # Start meeting at max(arrival, window_start)
        meet_start = max(arrival, w_start)
        # Check if we can meet for min_duration
        if meet_start + min_dur > w_end:
            continue
        
        # Schedule meeting
        meetings.append((name, loc, meet_start, meet_start + min_dur))
        count += 1
        total_duration += min_dur
        # Update current time and location
        current_time = meet_start + min_dur
        current_loc = loc
    
    # Evaluate this permutation
    if count > best_count or (count == best_count and total_duration > best_total_duration):
        best_count = count
        best_total_duration = total_duration
        best_meetings = meetings

# Convert best_meetings to required JSON format
itinerary = []
for name, loc, start_m, end_m in best_meetings:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(start_m),
        "end_time": minutes_to_time(end_m)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))