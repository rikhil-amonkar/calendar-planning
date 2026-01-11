import json
import itertools
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
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times in minutes: travel[from][to]
travel = {
    "Union Square": {
        "Nob Hill": 9,
        "Haight-Ashbury": 18,
        "Chinatown": 7,
        "Marina District": 18
    },
    "Nob Hill": {
        "Union Square": 7,
        "Haight-Ashbury": 13,
        "Chinatown": 6,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Union Square": 17,
        "Nob Hill": 15,
        "Chinatown": 19,
        "Marina District": 17
    },
    "Chinatown": {
        "Union Square": 7,
        "Nob Hill": 8,
        "Haight-Ashbury": 19,
        "Marina District": 12
    },
    "Marina District": {
        "Union Square": 16,
        "Nob Hill": 12,
        "Haight-Ashbury": 16,
        "Chinatown": 16
    }
}

# Friend data: name, location, available_start, available_end, min_duration (minutes)
friends = [
    ("Karen", "Nob Hill", "21:15", "21:45", 30),
    ("Joseph", "Haight-Ashbury", "12:30", "19:45", 90),
    ("Sandra", "Chinatown", "7:15", "19:15", 75),
    ("Nancy", "Marina District", "11:00", "20:15", 105)
]

# Convert to minutes for easier computation
friends_min = []
for name, loc, start, end, dur in friends:
    friends_min.append((name, loc, time_to_minutes(start), time_to_minutes(end), dur))

# Start at Union Square at 9:00 AM
current_time = time_to_minutes("9:00")
current_location = "Union Square"

best_schedule = None
best_idle = float('inf')

# Try all permutations of the 4 friends
for perm in itertools.permutations(range(4)):
    schedule = []
    feasible = True
    current_time = time_to_minutes("9:00")
    current_location = "Union Square"
    total_idle = 0
    
    for idx in perm:
        name, loc, avail_start, avail_end, dur = friends_min[idx]
        # Travel to friend's location
        travel_time = travel[current_location][loc]
        current_time += travel_time
        # Wait if we arrive before available start
        if current_time < avail_start:
            total_idle += (avail_start - current_time)
            current_time = avail_start
        # Check if we can meet for min duration
        if current_time + dur > avail_end:
            feasible = False
            break
        # Schedule meeting
        meeting_start = current_time
        meeting_end = current_time + dur
        schedule.append((name, loc, meeting_start, meeting_end))
        current_time = meeting_end
        current_location = loc
    
    if feasible:
        # Check if we want to minimize idle time or just pick first feasible
        if total_idle < best_idle:
            best_idle = total_idle
            best_schedule = schedule

# Convert best_schedule to required JSON format
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