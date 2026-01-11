import json
from itertools import permutations

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times dictionary: travel[from][to] = minutes
travel = {
    "Russian Hill": {
        "Marina District": 7, "Financial District": 11, "Alamo Square": 15,
        "Golden Gate Park": 21, "The Castro": 21, "Bayview": 23,
        "Sunset District": 23, "Haight-Ashbury": 17, "Nob Hill": 5
    },
    "Marina District": {
        "Russian Hill": 8, "Financial District": 17, "Alamo Square": 15,
        "Golden Gate Park": 18, "The Castro": 22, "Bayview": 27,
        "Sunset District": 19, "Haight-Ashbury": 16, "Nob Hill": 12
    },
    "Financial District": {
        "Russian Hill": 11, "Marina District": 15, "Alamo Square": 17,
        "Golden Gate Park": 23, "The Castro": 20, "Bayview": 19,
        "Sunset District": 30, "Haight-Ashbury": 19, "Nob Hill": 8
    },
    "Alamo Square": {
        "Russian Hill": 13, "Marina District": 15, "Financial District": 17,
        "Golden Gate Park": 9, "The Castro": 8, "Bayview": 16,
        "Sunset District": 16, "Haight-Ashbury": 5, "Nob Hill": 11
    },
    "Golden Gate Park": {
        "Russian Hill": 19, "Marina District": 16, "Financial District": 26,
        "Alamo Square": 9, "The Castro": 13, "Bayview": 23,
        "Sunset District": 10, "Haight-Ashbury": 7, "Nob Hill": 20
    },
    "The Castro": {
        "Russian Hill": 18, "Marina District": 21, "Financial District": 21,
        "Alamo Square": 8, "Golden Gate Park": 11, "Bayview": 19,
        "Sunset District": 17, "Haight-Ashbury": 6, "Nob Hill": 16
    },
    "Bayview": {
        "Russian Hill": 23, "Marina District": 27, "Financial District": 19,
        "Alamo Square": 16, "Golden Gate Park": 22, "The Castro": 19,
        "Sunset District": 23, "Haight-Ashbury": 19, "Nob Hill": 20
    },
    "Sunset District": {
        "Russian Hill": 24, "Marina District": 21, "Financial District": 30,
        "Alamo Square": 17, "Golden Gate Park": 11, "The Castro": 17,
        "Bayview": 22, "Haight-Ashbury": 15, "Nob Hill": 27
    },
    "Haight-Ashbury": {
        "Russian Hill": 17, "Marina District": 17, "Financial District": 21,
        "Alamo Square": 5, "Golden Gate Park": 7, "The Castro": 6,
        "Bayview": 18, "Sunset District": 15, "Nob Hill": 15
    },
    "Nob Hill": {
        "Russian Hill": 5, "Marina District": 11, "Financial District": 9,
        "Alamo Square": 11, "Golden Gate Park": 17, "The Castro": 17,
        "Bayview": 19, "Sunset District": 24, "Haight-Ashbury": 13
    }
}

# Friend data: name, location, start, end, min_duration (all in minutes from midnight)
friends = [
    ("Mark", "Marina District", time_to_minutes("18:45"), time_to_minutes("21:00"), 90),
    ("Karen", "Financial District", time_to_minutes("9:30"), time_to_minutes("12:45"), 90),
    ("Barbara", "Alamo Square", time_to_minutes("10:00"), time_to_minutes("19:30"), 90),
    ("Nancy", "Golden Gate Park", time_to_minutes("16:45"), time_to_minutes("20:00"), 105),
    ("David", "The Castro", time_to_minutes("9:00"), time_to_minutes("18:00"), 120),
    ("Linda", "Bayview", time_to_minutes("18:15"), time_to_minutes("19:45"), 45),
    ("Kevin", "Sunset District", time_to_minutes("10:00"), time_to_minutes("17:45"), 120),
    ("Matthew", "Haight-Ashbury", time_to_minutes("10:15"), time_to_minutes("15:30"), 45),
    ("Andrew", "Nob Hill", time_to_minutes("11:45"), time_to_minutes("16:45"), 105)
]

# Start at Russian Hill at 9:00 (which is 540 minutes from midnight)
start_time = time_to_minutes("9:00")
start_loc = "Russian Hill"

best_schedule = []
best_count = 0
best_total_minutes = 0

def backtrack(current_loc, current_time, met, schedule):
    global best_schedule, best_count, best_total_minutes
    # Try to add each un-met friend
    improved = False
    for idx, (name, loc, win_start, win_end, min_dur) in enumerate(friends):
        if met & (1 << idx):
            continue
        # Travel to friend's location
        travel_time = travel[current_loc][loc]
        arrive = current_time + travel_time
        # Start meeting at max(arrive, win_start)
        start_meeting = max(arrive, win_start)
        if start_meeting + min_dur <= win_end:
            # Can meet
            new_time = start_meeting + min_dur
            new_schedule = schedule + [(name, loc, start_meeting, new_time)]
            backtrack(loc, new_time, met | (1 << idx), new_schedule)
            improved = True
    # If no one else can be added, check if this is best
    if not improved:
        count = bin(met).count("1")
        total_minutes = sum(end - start for _, _, start, end in schedule)
        if count > best_count or (count == best_count and total_minutes > best_total_minutes):
            best_count = count
            best_total_minutes = total_minutes
            best_schedule = schedule

# Start backtracking
backtrack(start_loc, start_time, 0, [])

# Convert best_schedule to required JSON format
itinerary = []
for name, loc, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": loc,
        "person": name,
        "start_time": minutes_to_time(start_m),
        "end_time": minutes_to_time(end_m)
    })

# Output result
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))