import json
from itertools import permutations
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix
travel_times = {
    "Pacific Heights": {
        "Nob Hill": 8,
        "Russian Hill": 7,
        "The Castro": 16,
        "Sunset District": 21,
        "Haight-Ashbury": 11
    },
    "Nob Hill": {
        "Pacific Heights": 8,
        "Russian Hill": 5,
        "The Castro": 17,
        "Sunset District": 25,
        "Haight-Ashbury": 13
    },
    "Russian Hill": {
        "Pacific Heights": 7,
        "Nob Hill": 5,
        "The Castro": 21,
        "Sunset District": 23,
        "Haight-Ashbury": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Russian Hill": 18,
        "Sunset District": 17,
        "Haight-Ashbury": 6
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Nob Hill": 27,
        "Russian Hill": 24,
        "The Castro": 17,
        "Haight-Ashbury": 15
    },
    "Haight-Ashbury": {
        "Pacific Heights": 12,
        "Nob Hill": 15,
        "Russian Hill": 17,
        "The Castro": 6,
        "Sunset District": 15
    }
}

# Friend data: location, window start, window end, min duration (minutes)
friends = [
    ("Ronald", "Nob Hill", time_to_minutes("10:00"), time_to_minutes("17:00"), 105),
    ("Sarah", "Russian Hill", time_to_minutes("7:15"), time_to_minutes("9:30"), 45),
    ("Helen", "The Castro", time_to_minutes("13:30"), time_to_minutes("17:00"), 120),
    ("Joshua", "Sunset District", time_to_minutes("14:15"), time_to_minutes("19:30"), 90),
    ("Margaret", "Haight-Ashbury", time_to_minutes("10:15"), time_to_minutes("22:00"), 60)
]

# Remove Sarah because impossible (arrive at 9:07, leave 9:30, only 23 min < 45 min)
friends_possible = [f for f in friends if f[0] != "Sarah"]

# Start at Pacific Heights at 9:00
start_location = "Pacific Heights"
start_time = time_to_minutes("9:00")

best_schedule = None
best_count = 0

# Try all permutations of the 4 possible friends
for perm in permutations(friends_possible):
    current_location = start_location
    current_time = start_time
    schedule = []
    feasible = True
    
    for person, loc, win_start, win_end, min_dur in perm:
        # Travel to friend's location
        travel = travel_times[current_location][loc]
        arrival = current_time + travel
        
        # If we arrive before window start, wait
        start_meeting = max(arrival, win_start)
        # If we arrive after window end, impossible
        if start_meeting > win_end:
            feasible = False
            break
        
        end_meeting = start_meeting + min_dur
        if end_meeting > win_end:
            feasible = False
            break
        
        schedule.append((person, loc, start_meeting, end_meeting))
        current_location = loc
        current_time = end_meeting
    
    if feasible and len(schedule) > best_count:
        best_count = len(schedule)
        best_schedule = schedule

# Convert best schedule to output format
itinerary = []
for person, loc, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": person,
        "start_time": minutes_to_time(start_m),
        "end_time": minutes_to_time(end_m)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))