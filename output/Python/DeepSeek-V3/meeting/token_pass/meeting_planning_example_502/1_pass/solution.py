import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix
locations = ["Financial District", "Golden Gate Park", "Chinatown", "Union Square", "Fisherman's Wharf", "Pacific Heights", "North Beach"]
# Index mapping
loc_index = {loc: i for i, loc in enumerate(locations)}
travel_times = [[0]*7 for _ in range(7)]

# Fill matrix from given data
data = [
    [0, 23, 5, 9, 10, 13, 7],
    [26, 0, 23, 22, 24, 16, 24],
    [5, 23, 0, 7, 8, 10, 3],
    [9, 22, 7, 0, 15, 15, 10],
    [11, 25, 12, 13, 0, 12, 6],
    [13, 15, 11, 12, 13, 0, 9],
    [8, 22, 6, 7, 5, 8, 0]
]
for i in range(7):
    for j in range(7):
        travel_times[i][j] = data[i][j]

# Friends data: name, location, start, end, min_duration
friends = [
    ("Stephanie", "Golden Gate Park", "11:00", "15:00", 105),
    ("Karen", "Chinatown", "13:45", "16:30", 15),
    ("Brian", "Union Square", "15:00", "17:15", 30),
    ("Rebecca", "Fisherman's Wharf", "8:00", "11:15", 30),
    ("Joseph", "Pacific Heights", "8:15", "9:30", 60),
    ("Steven", "North Beach", "14:30", "20:45", 120)
]

# Convert times to minutes
friends_min = []
for name, loc, start, end, dur in friends:
    friends_min.append((
        name,
        loc,
        time_to_minutes(start),
        time_to_minutes(end),
        dur
    ))

# Exclude Joseph (impossible to meet given start at 9:00)
friends_min = [f for f in friends_min if f[0] != "Joseph"]

# Start at Financial District at 9:00
current_time = time_to_minutes("9:00")
current_loc = "Financial District"

# Try all permutations of the 5 friends
best_meetings = []
best_total_duration = 0
best_schedule = []

for perm in itertools.permutations(range(len(friends_min))):
    schedule = []
    ct = current_time
    cl = current_loc
    possible = True
    total_duration = 0
    meetings = []
    
    for idx in perm:
        name, loc, start, end, dur = friends_min[idx]
        travel = travel_times[loc_index[cl]][loc_index[loc]]
        arrive = ct + travel
        # If arrive before start, wait
        if arrive < start:
            arrive = start
        # If arrive too late to meet for dur before end
        if arrive + dur > end:
            possible = False
            break
        # Meet
        meetings.append((name, loc, arrive, arrive + dur))
        total_duration += dur
        ct = arrive + dur
        cl = loc
    
    if possible and len(meetings) >= len(best_meetings):
        if len(meetings) > len(best_meetings) or total_duration > best_total_duration:
            best_meetings = meetings
            best_total_duration = total_duration
            best_schedule = perm

# Convert best_meetings to itinerary
itinerary = []
for name, loc, start, end in best_meetings:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })

# Output JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))