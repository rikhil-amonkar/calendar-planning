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
    """Convert minutes since midnight to 'H:MM' format."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times matrix
travel_times = {
    "Marina District": {
        "Richmond District": 11,
        "Union Square": 16,
        "Nob Hill": 12,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Financial District": 17,
        "North Beach": 11,
        "Presidio": 10,
    },
    "Richmond District": {
        "Marina District": 9,
        "Union Square": 21,
        "Nob Hill": 17,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "North Beach": 17,
        "Presidio": 7,
    },
    "Union Square": {
        "Marina District": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Fisherman's Wharf": 15,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Financial District": 9,
        "North Beach": 10,
        "Presidio": 24,
    },
    "Nob Hill": {
        "Marina District": 11,
        "Richmond District": 14,
        "Union Square": 7,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Financial District": 9,
        "North Beach": 8,
        "Presidio": 17,
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Financial District": 11,
        "North Beach": 6,
        "Presidio": 17,
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 20,
        "Fisherman's Wharf": 24,
        "Embarcadero": 25,
        "Financial District": 26,
        "North Beach": 23,
        "Presidio": 11,
    },
    "Embarcadero": {
        "Marina District": 12,
        "Richmond District": 21,
        "Union Square": 10,
        "Nob Hill": 10,
        "Fisherman's Wharf": 6,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20,
    },
    "Financial District": {
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Nob Hill": 8,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "North Beach": 7,
        "Presidio": 22,
    },
    "North Beach": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 7,
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Financial District": 8,
        "Presidio": 17,
    },
    "Presidio": {
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Financial District": 23,
        "North Beach": 18,
    },
}

# Friends data: name, location, window start, window end, min_duration (minutes)
friends = [
    ("Stephanie", "Richmond District", "16:15", "21:30", 75),
    ("William", "Union Square", "10:45", "17:30", 45),
    ("Elizabeth", "Nob Hill", "12:15", "15:00", 105),
    ("Joseph", "Fisherman's Wharf", "12:45", "14:00", 75),
    ("Anthony", "Golden Gate Park", "13:00", "20:30", 75),
    ("Barbara", "Embarcadero", "19:15", "20:30", 75),
    ("Carol", "Financial District", "11:45", "16:15", 60),
    ("Sandra", "North Beach", "10:00", "12:30", 15),
    ("Kenneth", "Presidio", "21:15", "22:15", 45),
]

# Convert times to minutes
friends_min = []
for name, loc, start, end, dur in friends:
    friends_min.append((name, loc, time_to_minutes(start), time_to_minutes(end), dur))

start_location = "Marina District"
start_time = time_to_minutes("9:00")

# Try all permutations
best_count = 0
best_total_time = 0
best_schedule = []

all_friends_indices = list(range(len(friends_min)))

for perm in itertools.permutations(all_friends_indices):
    current_loc = start_location
    current_time = start_time
    meetings = []
    feasible = True
    
    for idx in perm:
        name, loc, win_start, win_end, min_dur = friends_min[idx]
        travel = travel_times[current_loc][loc]
        arrive = current_time + travel
        
        if arrive > win_end:
            feasible = False
            break
        
        start_meet = max(arrive, win_start)
        if start_meet + min_dur > win_end:
            feasible = False
            break
        
        end_meet = start_meet + min_dur
        meetings.append((name, loc, start_meet, end_meet))
        
        current_loc = loc
        current_time = end_meet
    
    if feasible:
        count = len(meetings)
        total_time = sum(end - start for _, _, start, end in meetings)
        if count > best_count or (count == best_count and total_time > best_total_time):
            best_count = count
            best_total_time = total_time
            best_schedule = meetings

# Convert best schedule to output format
itinerary = []
for name, loc, start, end in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))