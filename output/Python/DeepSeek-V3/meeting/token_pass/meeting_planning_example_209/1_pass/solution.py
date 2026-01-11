import json
from itertools import permutations

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t  # if already int

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes
travel = {
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
}

# Friend data: name, location, window_start, window_end, desired_duration (minutes)
friends = [
    ("Melissa", "North Beach", "8:15", "13:30", 105),
    ("Anthony", "Chinatown", "13:15", "14:30", 60),
    ("Rebecca", "Russian Hill", "19:30", "21:15", 105),
]

# Convert times to minutes for easier computation
friends_min = []
for name, loc, start, end, dur in friends:
    friends_min.append((name, loc, time_to_minutes(start), time_to_minutes(end), dur))

# Start at Sunset District at 9:00 AM
current_location = "Sunset District"
current_time = time_to_minutes("9:00")

best_schedule = None
best_met = 0

# Try all meeting orders
for perm in permutations(range(len(friends_min))):
    schedule = []
    loc = current_location
    time = current_time
    met_count = 0
    feasible = True
    
    for idx in perm:
        name, loc2, start, end, dur = friends_min[idx]
        # Travel to friend's location
        travel_time = travel.get((loc, loc2))
        if travel_time is None:
            travel_time = travel.get((loc, loc2))  # should exist
        time += travel_time
        # Start meeting at max(time, start), but must finish by end
        meet_start = max(time, start)
        if meet_start + dur > end:
            feasible = False
            break
        # Record meeting
        schedule.append((name, loc2, meet_start, meet_start + dur))
        # Update after meeting
        time = meet_start + dur
        loc = loc2
        met_count += 1
    
    if feasible and met_count > best_met:
        best_met = met_count
        best_schedule = schedule

# Convert best schedule to required JSON format
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