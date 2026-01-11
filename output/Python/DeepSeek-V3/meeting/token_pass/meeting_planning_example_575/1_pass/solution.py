import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MMAM/PM' to minutes since midnight."""
    # Input format like '9:00AM' or '6:15PM'
    # But here we'll handle 24-hour-like given in constraints: e.g., '9:00', '13:30'
    # Actually, constraints are given like '9:00AM' in text, but in code we'll parse as 12-hour with AM/PM.
    # Let's adapt: given in problem statement as e.g., "9:00AM" or "6:15PM"
    # We'll parse accordingly.
    if isinstance(t, str):
        if 'AM' in t or 'PM' in t:
            return int(datetime.strptime(t, '%I:%M%p').strftime('%H')) * 60 + int(datetime.strptime(t, '%I:%M%p').strftime('%M'))
        else:
            # 24-hour format without AM/PM
            h, m = map(int, t.split(':'))
            return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix (in minutes)
locations = ["The Castro", "Presidio", "Sunset District", "Haight-Ashbury", "Mission District", "Golden Gate Park", "Russian Hill"]
# Map location to index
loc_index = {loc: i for i, loc in enumerate(locations)}

# Travel times given as from->to pairs
# We'll create a 7x7 matrix
travel_matrix = [[0]*7 for _ in range(7)]

# Fill from given data (only given pairs, assume symmetric if not given? But we have all pairs in problem statement)
# Let's enter manually from the list:
pairs = [
    ("The Castro", "Presidio", 20),
    ("The Castro", "Sunset District", 17),
    ("The Castro", "Haight-Ashbury", 6),
    ("The Castro", "Mission District", 7),
    ("The Castro", "Golden Gate Park", 11),
    ("The Castro", "Russian Hill", 18),
    ("Presidio", "The Castro", 21),
    ("Presidio", "Sunset District", 15),
    ("Presidio", "Haight-Ashbury", 15),
    ("Presidio", "Mission District", 26),
    ("Presidio", "Golden Gate Park", 12),
    ("Presidio", "Russian Hill", 14),
    ("Sunset District", "The Castro", 17),
    ("Sunset District", "Presidio", 16),
    ("Sunset District", "Haight-Ashbury", 15),
    ("Sunset District", "Mission District", 24),
    ("Sunset District", "Golden Gate Park", 11),
    ("Sunset District", "Russian Hill", 24),
    ("Haight-Ashbury", "The Castro", 6),
    ("Haight-Ashbury", "Presidio", 15),
    ("Haight-Ashbury", "Sunset District", 15),
    ("Haight-Ashbury", "Mission District", 11),
    ("Haight-Ashbury", "Golden Gate Park", 7),
    ("Haight-Ashbury", "Russian Hill", 17),
    ("Mission District", "The Castro", 7),
    ("Mission District", "Presidio", 25),
    ("Mission District", "Sunset District", 24),
    ("Mission District", "Haight-Ashbury", 12),
    ("Mission District", "Golden Gate Park", 17),
    ("Mission District", "Russian Hill", 15),
    ("Golden Gate Park", "The Castro", 13),
    ("Golden Gate Park", "Presidio", 11),
    ("Golden Gate Park", "Sunset District", 10),
    ("Golden Gate Park", "Haight-Ashbury", 7),
    ("Golden Gate Park", "Mission District", 17),
    ("Golden Gate Park", "Russian Hill", 19),
    ("Russian Hill", "The Castro", 21),
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "Sunset District", 23),
    ("Russian Hill", "Haight-Ashbury", 17),
    ("Russian Hill", "Mission District", 16),
    ("Russian Hill", "Golden Gate Park", 21),
]

for from_loc, to_loc, t in pairs:
    travel_matrix[loc_index[from_loc]][loc_index[to_loc]] = t

# Friends data: name, location, window start, window end, min duration (minutes)
friends = [
    ("Rebecca", "Presidio", "6:15PM", "8:45PM", 60),
    ("Linda", "Sunset District", "3:30PM", "7:45PM", 30),
    ("Elizabeth", "Haight-Ashbury", "5:15PM", "7:30PM", 105),
    ("William", "Mission District", "1:15PM", "7:30PM", 30),
    ("Robert", "Golden Gate Park", "2:15PM", "9:30PM", 45),
    ("Mark", "Russian Hill", "10:00AM", "9:15PM", 75),
]

# Convert times to minutes
friends_min = []
for name, loc, start, end, dur in friends:
    friends_min.append((name, loc, time_to_minutes(start), time_to_minutes(end), dur))

# Start: at The Castro at 9:00 AM
start_time = time_to_minutes("9:00AM")
start_loc = "The Castro"

# Try all permutations of friends
best_count = 0
best_total_duration = 0
best_schedule = []

for perm in itertools.permutations(range(len(friends))):
    current_time = start_time
    current_loc_index = loc_index[start_loc]
    met_count = 0
    schedule = []
    possible = True
    total_duration = 0
    
    for idx in perm:
        name, loc, win_start, win_end, min_dur = friends_min[idx]
        to_loc_index = loc_index[loc]
        travel_time = travel_matrix[current_loc_index][to_loc_index]
        arrival_time = current_time + travel_time
        
        if arrival_time > win_end:
            possible = False
            break
        
        start_meeting = max(arrival_time, win_start)
        if start_meeting + min_dur > win_end:
            possible = False
            break
        
        end_meeting = start_meeting + min_dur
        schedule.append((name, loc, start_meeting, end_meeting))
        total_duration += min_dur
        met_count += 1
        current_time = end_meeting
        current_loc_index = to_loc_index
    
    if possible:
        if met_count > best_count or (met_count == best_count and total_duration > best_total_duration):
            best_count = met_count
            best_total_duration = total_duration
            best_schedule = schedule

# Convert best_schedule to output format
itinerary = []
for name, loc, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(start_m),
        "end_time": minutes_to_time(end_m)
    })

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))