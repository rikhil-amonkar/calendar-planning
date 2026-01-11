import json
import itertools
from collections import defaultdict

def time_to_min(timestr):
    """Convert 'H:MM' or 'HH:MM' to minutes since midnight."""
    if isinstance(timestr, str):
        h, m = map(int, timestr.split(':'))
        return h * 60 + m
    return timestr

def min_to_time(m):
    """Convert minutes since midnight to 'H:MM' format."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times in minutes: from_location -> to_location -> time
travel = defaultdict(dict)

locations = ["Russian Hill", "Presidio", "Chinatown", "Pacific Heights", 
             "Richmond District", "Fisherman's Wharf", "Golden Gate Park", "Bayview"]

# Fill travel times from given data
data = [
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "Chinatown", 9),
    ("Russian Hill", "Pacific Heights", 7),
    ("Russian Hill", "Richmond District", 14),
    ("Russian Hill", "Fisherman's Wharf", 7),
    ("Russian Hill", "Golden Gate Park", 21),
    ("Russian Hill", "Bayview", 23),
    ("Presidio", "Russian Hill", 14),
    ("Presidio", "Chinatown", 21),
    ("Presidio", "Pacific Heights", 11),
    ("Presidio", "Richmond District", 7),
    ("Presidio", "Fisherman's Wharf", 19),
    ("Presidio", "Golden Gate Park", 12),
    ("Presidio", "Bayview", 31),
    ("Chinatown", "Russian Hill", 7),
    ("Chinatown", "Presidio", 19),
    ("Chinatown", "Pacific Heights", 10),
    ("Chinatown", "Richmond District", 20),
    ("Chinatown", "Fisherman's Wharf", 8),
    ("Chinatown", "Golden Gate Park", 23),
    ("Chinatown", "Bayview", 22),
    ("Pacific Heights", "Russian Hill", 7),
    ("Pacific Heights", "Presidio", 11),
    ("Pacific Heights", "Chinatown", 11),
    ("Pacific Heights", "Richmond District", 12),
    ("Pacific Heights", "Fisherman's Wharf", 13),
    ("Pacific Heights", "Golden Gate Park", 15),
    ("Pacific Heights", "Bayview", 22),
    ("Richmond District", "Russian Hill", 13),
    ("Richmond District", "Presidio", 7),
    ("Richmond District", "Chinatown", 20),
    ("Richmond District", "Pacific Heights", 10),
    ("Richmond District", "Fisherman's Wharf", 18),
    ("Richmond District", "Golden Gate Park", 9),
    ("Richmond District", "Bayview", 26),
    ("Fisherman's Wharf", "Russian Hill", 7),
    ("Fisherman's Wharf", "Presidio", 17),
    ("Fisherman's Wharf", "Chinatown", 12),
    ("Fisherman's Wharf", "Pacific Heights", 12),
    ("Fisherman's Wharf", "Richmond District", 18),
    ("Fisherman's Wharf", "Golden Gate Park", 25),
    ("Fisherman's Wharf", "Bayview", 26),
    ("Golden Gate Park", "Russian Hill", 19),
    ("Golden Gate Park", "Presidio", 11),
    ("Golden Gate Park", "Chinatown", 23),
    ("Golden Gate Park", "Pacific Heights", 16),
    ("Golden Gate Park", "Richmond District", 7),
    ("Golden Gate Park", "Fisherman's Wharf", 24),
    ("Golden Gate Park", "Bayview", 23),
    ("Bayview", "Russian Hill", 23),
    ("Bayview", "Presidio", 31),
    ("Bayview", "Chinatown", 18),
    ("Bayview", "Pacific Heights", 23),
    ("Bayview", "Richmond District", 25),
    ("Bayview", "Fisherman's Wharf", 25),
    ("Bayview", "Golden Gate Park", 22),
]

for f, t, d in data:
    travel[f][t] = d

# Friends data: name -> (location, window_start, window_end, min_duration_minutes)
friends = {
    "Matthew":  ("Presidio",          time_to_min("11:00"), time_to_min("21:00"), 90),
    "Margaret": ("Chinatown",         time_to_min("9:15"),  time_to_min("18:45"), 90),
    "Nancy":    ("Pacific Heights",   time_to_min("14:15"), time_to_min("17:00"), 15),
    "Helen":    ("Richmond District", time_to_min("19:45"), time_to_min("22:00"), 60),
    "Rebecca":  ("Fisherman's Wharf", time_to_min("21:15"), time_to_min("22:15"), 60),
    "Kimberly": ("Golden Gate Park",  time_to_min("13:00"), time_to_min("16:30"), 120),
    "Kenneth":  ("Bayview",           time_to_min("14:30"), time_to_min("18:00"), 60),
}

# Start at Russian Hill at 9:00 AM
start_time = time_to_min("9:00")
start_loc = "Russian Hill"

best_count = 0
best_meetings = []
best_total_time = 0

# Try all permutations of the 7 friends
for perm in itertools.permutations(friends.keys()):
    current_time = start_time
    current_loc = start_loc
    meetings = []
    count = 0
    
    for name in perm:
        loc, win_start, win_end, dur = friends[name]
        # Travel to friend's location
        travel_time = travel[current_loc][loc]
        arrive_time = current_time + travel_time
        
        # If arrive before window, wait until window starts
        start_meeting = max(arrive_time, win_start)
        # If start too late to get min duration, skip this friend
        if start_meeting + dur > win_end:
            continue
        
        # Schedule meeting
        end_meeting = start_meeting + dur
        meetings.append((name, loc, start_meeting, end_meeting))
        count += 1
        current_time = end_meeting
        current_loc = loc
    
    # Evaluate this permutation
    if count > best_count:
        best_count = count
        best_meetings = meetings
        best_total_time = sum(m[3] - m[2] for m in meetings)
    elif count == best_count and count > 0:
        total_time = sum(m[3] - m[2] for m in meetings)
        if total_time > best_total_time:
            best_meetings = meetings
            best_total_time = total_time

# Convert best_meetings to required JSON format
itinerary = []
for name, loc, start_m, end_m in best_meetings:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": min_to_time(start_m),
        "end_time": min_to_time(end_m)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))