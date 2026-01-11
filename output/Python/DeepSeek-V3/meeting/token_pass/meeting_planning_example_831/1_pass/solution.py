import json
from itertools import permutations

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

# Travel times matrix (in minutes)
locations = [
    "Presidio",
    "Fisherman's Wharf",
    "Alamo Square",
    "Financial District",
    "Union Square",
    "Sunset District",
    "Embarcadero",
    "Golden Gate Park",
    "Chinatown",
    "Richmond District"
]
loc_index = {loc: i for i, loc in enumerate(locations)}

# Asymmetric travel times from the given data
travel_matrix = [
    [0, 19, 19, 23, 22, 15, 20, 12, 21, 7],   # Presidio
    [17, 0, 21, 11, 13, 27, 8, 25, 12, 18],   # Fisherman's Wharf
    [17, 19, 0, 17, 14, 16, 16, 9, 15, 11],   # Alamo Square
    [22, 10, 17, 0, 9, 30, 4, 23, 5, 21],     # Financial District
    [24, 15, 15, 9, 0, 27, 11, 22, 7, 20],    # Union Square
    [16, 29, 17, 30, 30, 0, 30, 11, 30, 12],  # Sunset District
    [20, 6, 19, 5, 10, 30, 0, 25, 7, 21],     # Embarcadero
    [11, 24, 9, 26, 22, 10, 25, 0, 23, 7],    # Golden Gate Park
    [19, 8, 17, 5, 7, 29, 5, 23, 0, 20],      # Chinatown
    [7, 18, 13, 22, 21, 11, 19, 9, 20, 0]     # Richmond District
]

def travel_time(from_loc, to_loc):
    return travel_matrix[loc_index[from_loc]][loc_index[to_loc]]

# Friends data: name, location, window start, window end, min_duration (minutes)
friends = [
    ("Jeffrey", "Fisherman's Wharf", "10:15", "13:00", 90),
    ("Ronald", "Alamo Square", "7:45", "14:45", 120),
    ("Jason", "Financial District", "10:45", "16:00", 105),
    ("Melissa", "Union Square", "17:45", "18:15", 15),
    ("Elizabeth", "Sunset District", "14:45", "17:30", 105),
    ("Margaret", "Embarcadero", "13:15", "19:00", 90),
    ("George", "Golden Gate Park", "19:00", "22:00", 75),
    ("Richard", "Chinatown", "9:30", "21:00", 15),
    ("Laura", "Richmond District", "9:45", "18:00", 60)
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

# Search
best_count = 0
best_itinerary = []
best_meetings = []

def dfs(current_loc, current_time, met, itinerary, remaining):
    global best_count, best_itinerary, best_meetings
    # If no remaining friends, check if this is best
    if len(met) > best_count:
        best_count = len(met)
        best_itinerary = itinerary[:]
        best_meetings = met[:]
    # Try each remaining friend
    for i, (name, loc, start, end, dur) in enumerate(remaining):
        # Travel to friend
        travel = travel_time(current_loc, loc)
        arrive = current_time + travel
        # Start meeting at max(arrive, friend's start time)
        meet_start = max(arrive, start)
        # Check if feasible
        if meet_start + dur <= end:
            new_time = meet_start + dur
            new_met = met + [(name, loc, meet_start, new_time)]
            new_itinerary = itinerary + [{
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(new_time)
            }]
            dfs(loc, new_time, new_met, new_itinerary, remaining[:i] + remaining[i+1:])

# Start search
start_loc = "Presidio"
start_time = time_to_minutes("9:00")
dfs(start_loc, start_time, [], [], friends_min)

# Output result
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))