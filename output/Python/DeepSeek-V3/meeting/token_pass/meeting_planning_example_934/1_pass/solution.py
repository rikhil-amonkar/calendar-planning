import json
from itertools import permutations
from copy import deepcopy

# Convert time string "H:MM" to minutes since midnight
def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

# Locations
locations = [
    "Nob Hill", "Embarcadero", "The Castro", "Haight-Ashbury",
    "Union Square", "North Beach", "Pacific Heights", "Chinatown",
    "Golden Gate Park", "Marina District", "Russian Hill"
]
loc_index = {loc: i for i, loc in enumerate(locations)}

# Travel times matrix (from_index, to_index) -> minutes
# We'll build from given data
travel = [[0]*11 for _ in range(11)]

# Fill from given pairs (only one direction per given, but we need both ways)
# We'll enter all given, then assume symmetric if not given (but problem gives both ways for each pair? Let's check)
# Actually, they gave both directions for each pair already, so we'll just parse all.

pairs = [
    ("Nob Hill", "Embarcadero", 9), ("Nob Hill", "The Castro", 17),
    ("Nob Hill", "Haight-Ashbury", 13), ("Nob Hill", "Union Square", 7),
    ("Nob Hill", "North Beach", 8), ("Nob Hill", "Pacific Heights", 8),
    ("Nob Hill", "Chinatown", 6), ("Nob Hill", "Golden Gate Park", 17),
    ("Nob Hill", "Marina District", 11), ("Nob Hill", "Russian Hill", 5),
    ("Embarcadero", "Nob Hill", 10), ("Embarcadero", "The Castro", 25),
    ("Embarcadero", "Haight-Ashbury", 21), ("Embarcadero", "Union Square", 10),
    ("Embarcadero", "North Beach", 5), ("Embarcadero", "Pacific Heights", 11),
    ("Embarcadero", "Chinatown", 7), ("Embarcadero", "Golden Gate Park", 25),
    ("Embarcadero", "Marina District", 12), ("Embarcadero", "Russian Hill", 8),
    ("The Castro", "Nob Hill", 16), ("The Castro", "Embarcadero", 22),
    ("The Castro", "Haight-Ashbury", 6), ("The Castro", "Union Square", 19),
    ("The Castro", "North Beach", 20), ("The Castro", "Pacific Heights", 16),
    ("The Castro", "Chinatown", 22), ("The Castro", "Golden Gate Park", 11),
    ("The Castro", "Marina District", 21), ("The Castro", "Russian Hill", 18),
    ("Haight-Ashbury", "Nob Hill", 15), ("Haight-Ashbury", "Embarcadero", 20),
    ("Haight-Ashbury", "The Castro", 6), ("Haight-Ashbury", "Union Square", 19),
    ("Haight-Ashbury", "North Beach", 19), ("Haight-Ashbury", "Pacific Heights", 12),
    ("Haight-Ashbury", "Chinatown", 19), ("Haight-Ashbury", "Golden Gate Park", 7),
    ("Haight-Ashbury", "Marina District", 17), ("Haight-Ashbury", "Russian Hill", 17),
    ("Union Square", "Nob Hill", 9), ("Union Square", "Embarcadero", 11),
    ("Union Square", "The Castro", 17), ("Union Square", "Haight-Ashbury", 18),
    ("Union Square", "North Beach", 10), ("Union Square", "Pacific Heights", 15),
    ("Union Square", "Chinatown", 7), ("Union Square", "Golden Gate Park", 22),
    ("Union Square", "Marina District", 18), ("Union Square", "Russian Hill", 13),
    ("North Beach", "Nob Hill", 7), ("North Beach", "Embarcadero", 6),
    ("North Beach", "The Castro", 23), ("North Beach", "Haight-Ashbury", 18),
    ("North Beach", "Union Square", 7), ("North Beach", "Pacific Heights", 8),
    ("North Beach", "Chinatown", 6), ("North Beach", "Golden Gate Park", 22),
    ("North Beach", "Marina District", 9), ("North Beach", "Russian Hill", 4),
    ("Pacific Heights", "Nob Hill", 8), ("Pacific Heights", "Embarcadero", 10),
    ("Pacific Heights", "The Castro", 16), ("Pacific Heights", "Haight-Ashbury", 11),
    ("Pacific Heights", "Union Square", 12), ("Pacific Heights", "North Beach", 9),
    ("Pacific Heights", "Chinatown", 11), ("Pacific Heights", "Golden Gate Park", 15),
    ("Pacific Heights", "Marina District", 6), ("Pacific Heights", "Russian Hill", 7),
    ("Chinatown", "Nob Hill", 9), ("Chinatown", "Embarcadero", 5),
    ("Chinatown", "The Castro", 22), ("Chinatown", "Haight-Ashbury", 19),
    ("Chinatown", "Union Square", 7), ("Chinatown", "North Beach", 3),
    ("Chinatown", "Pacific Heights", 10), ("Chinatown", "Golden Gate Park", 23),
    ("Chinatown", "Marina District", 12), ("Chinatown", "Russian Hill", 7),
    ("Golden Gate Park", "Nob Hill", 20), ("Golden Gate Park", "Embarcadero", 25),
    ("Golden Gate Park", "The Castro", 13), ("Golden Gate Park", "Haight-Ashbury", 7),
    ("Golden Gate Park", "Union Square", 22), ("Golden Gate Park", "North Beach", 23),
    ("Golden Gate Park", "Pacific Heights", 16), ("Golden Gate Park", "Chinatown", 23),
    ("Golden Gate Park", "Marina District", 16), ("Golden Gate Park", "Russian Hill", 19),
    ("Marina District", "Nob Hill", 12), ("Marina District", "Embarcadero", 14),
    ("Marina District", "The Castro", 22), ("Marina District", "Haight-Ashbury", 16),
    ("Marina District", "Union Square", 16), ("Marina District", "North Beach", 11),
    ("Marina District", "Pacific Heights", 7), ("Marina District", "Chinatown", 15),
    ("Marina District", "Golden Gate Park", 18), ("Marina District", "Russian Hill", 8),
    ("Russian Hill", "Nob Hill", 5), ("Russian Hill", "Embarcadero", 8),
    ("Russian Hill", "The Castro", 21), ("Russian Hill", "Haight-Ashbury", 17),
    ("Russian Hill", "Union Square", 10), ("Russian Hill", "North Beach", 5),
    ("Russian Hill", "Pacific Heights", 7), ("Russian Hill", "Chinatown", 9),
    ("Russian Hill", "Golden Gate Park", 21), ("Russian Hill", "Marina District", 7)
]

for a, b, t in pairs:
    travel[loc_index[a]][loc_index[b]] = t

# Friends data: name, location, window start, window end, min desired minutes
friends = [
    ("Mary", "Embarcadero", "20:00", "21:15", 75),
    ("Kenneth", "The Castro", "11:15", "19:15", 30),
    ("Joseph", "Haight-Ashbury", "20:00", "22:00", 120),
    ("Sarah", "Union Square", "11:45", "14:30", 90),
    ("Thomas", "North Beach", "19:15", "19:45", 15),
    ("Daniel", "Pacific Heights", "13:45", "20:30", 15),
    ("Richard", "Chinatown", "8:00", "18:45", 30),
    ("Mark", "Golden Gate Park", "17:30", "21:30", 120),
    ("David", "Marina District", "20:00", "21:00", 60),
    ("Karen", "Russian Hill", "13:15", "18:30", 120)
]

# Convert times to minutes since midnight
friends_data = []
for name, loc, start, end, dur in friends:
    friends_data.append({
        "name": name,
        "loc_idx": loc_index[loc],
        "start": time_to_min(start),
        "end": time_to_min(end),
        "min_dur": dur
    })

# Search
start_time = time_to_min("9:00")
start_loc = loc_index["Nob Hill"]

best_count = -1
best_total_dur = -1
best_schedule = []

def dfs(visited, current_time, current_loc, schedule, remaining):
    global best_count, best_total_dur, best_schedule
    
    # Try to add each unvisited friend
    for i in range(len(friends_data)):
        if i in visited:
            continue
        f = friends_data[i]
        travel_time = travel[current_loc][f["loc_idx"]]
        arrival = current_time + travel_time
        start_meeting = max(arrival, f["start"])
        if start_meeting + f["min_dur"] > f["end"]:
            continue  # can't meet min duration
        
        # Meet for exactly min duration (greedy for count)
        end_meeting = start_meeting + f["min_dur"]
        
        new_schedule = schedule + [(i, start_meeting, end_meeting)]
        new_visited = visited | {i}
        
        if len(new_visited) > best_count or (len(new_visited) == best_count and sum(end - start for _, start, end in new_schedule) > best_total_dur):
            best_count = len(new_visited)
            best_total_dur = sum(end - start for _, start, end in new_schedule)
            best_schedule = new_schedule[:]
        
        dfs(new_visited, end_meeting, f["loc_idx"], new_schedule, remaining - 1)

# Start search
dfs(set(), start_time, start_loc, [], len(friends_data))

# Convert best_schedule to itinerary
itinerary = []
for idx, start_m, end_m in best_schedule:
    f = friends_data[idx]
    itinerary.append({
        "action": "meet",
        "location": locations[f["loc_idx"]],
        "person": f["name"],
        "start_time": min_to_time(start_m),
        "end_time": min_to_time(end_m)
    })

# Output
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))