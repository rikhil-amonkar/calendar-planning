import json

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Input variables
start_location = "Haight-Ashbury"
start_time_str = "9:00"

people = [
    {"name": "Elizabeth", "location": "Mission District", "start": "10:30", "end": "20:00", "duration": 90},
    {"name": "David", "location": "Union Square", "start": "15:15", "end": "19:00", "duration": 45},
    {"name": "Sandra", "location": "Pacific Heights", "start": "7:00", "end": "20:00", "duration": 120},
    {"name": "Thomas", "location": "Bayview", "start": "19:30", "end": "20:30", "duration": 30},
    {"name": "Robert", "location": "Fisherman's Wharf", "start": "10:00", "end": "15:00", "duration": 15},
    {"name": "Kenneth", "location": "Marina District", "start": "10:45", "end": "13:00", "duration": 45},
    {"name": "Melissa", "location": "Richmond District", "start": "18:15", "end": "20:00", "duration": 15},
    {"name": "Kimberly", "location": "Sunset District", "start": "10:15", "end": "18:15", "duration": 105},
    {"name": "Amanda", "location": "Golden Gate Park", "start": "7:45", "end": "18:45", "duration": 15},
]

# Convert times to minutes
for p in people:
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

start_time = time_to_minutes(start_time_str)

# Travel times (directed, in minutes)
TT = {
    "Haight-Ashbury": {
        "Mission District": 11, "Union Square": 19, "Pacific Heights": 12, "Bayview": 18,
        "Fisherman's Wharf": 23, "Marina District": 17, "Richmond District": 10,
        "Sunset District": 15, "Golden Gate Park": 7
    },
    "Mission District": {
        "Haight-Ashbury": 12, "Union Square": 15, "Pacific Heights": 16, "Bayview": 14,
        "Fisherman's Wharf": 22, "Marina District": 19, "Richmond District": 20,
        "Sunset District": 24, "Golden Gate Park": 17
    },
    "Union Square": {
        "Haight-Ashbury": 18, "Mission District": 14, "Pacific Heights": 15, "Bayview": 15,
        "Fisherman's Wharf": 15, "Marina District": 18, "Richmond District": 20,
        "Sunset District": 27, "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11, "Mission District": 15, "Union Square": 12, "Bayview": 22,
        "Fisherman's Wharf": 13, "Marina District": 6, "Richmond District": 12,
        "Sunset District": 21, "Golden Gate Park": 15
    },
    "Bayview": {
        "Haight-Ashbury": 19, "Mission District": 13, "Union Square": 18, "Pacific Heights": 23,
        "Fisherman's Wharf": 25, "Marina District": 27, "Richmond District": 25,
        "Sunset District": 23, "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22, "Mission District": 22, "Union Square": 13, "Pacific Heights": 12,
        "Bayview": 26, "Marina District": 9, "Richmond District": 18,
        "Sunset District": 27, "Golden Gate Park": 25
    },
    "Marina District": {
        "Haight-Ashbury": 16, "Mission District": 20, "Union Square": 16, "Pacific Heights": 7,
        "Bayview": 27, "Fisherman's Wharf": 10, "Richmond District": 11,
        "Sunset District": 19, "Golden Gate Park": 18
    },
    "Richmond District": {
        "Haight-Ashbury": 10, "Mission District": 20, "Union Square": 21, "Pacific Heights": 10,
        "Bayview": 27, "Fisherman's Wharf": 18, "Marina District": 9,
        "Sunset District": 11, "Golden Gate Park": 9
    },
    "Sunset District": {
        "Haight-Ashbury": 15, "Mission District": 25, "Union Square": 30, "Pacific Heights": 21,
        "Bayview": 22, "Fisherman's Wharf": 29, "Marina District": 21,
        "Richmond District": 12, "Golden Gate Park": 11
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7, "Mission District": 17, "Union Square": 22, "Pacific Heights": 16,
        "Bayview": 23, "Fisherman's Wharf": 24, "Marina District": 16,
        "Richmond District": 7, "Sunset District": 10
    },
}

locations = set(TT.keys())

def travel_time(a, b):
    if a == b:
        return 0
    return TT[a][b]

# Precompute index mapping
name_to_index = {p["name"]: i for i in people}
N = len(people)

best_itinerary = []
best_count = 0
full_found = False

def possible_now_count(curr_loc, curr_time, visited_mask):
    cnt = 0
    for i, p in enumerate(people):
        if (visited_mask >> i) & 1:
            continue
        t = curr_time + travel_time(curr_loc, p["location"])
        start = max(t, p["start_min"])
        end = start + p["duration"]
        if end <= p["end_min"]:
            cnt += 1
    return cnt

def dfs(curr_loc, curr_time, visited_mask, path):
    global best_itinerary, best_count, full_found
    curr_count = len(path)
    # Update best
    if curr_count > best_count:
        best_count = curr_count
        best_itinerary = path.copy()
        if best_count == N:
            full_found = True
            return

    # Upper bound pruning
    possible_more = possible_now_count(curr_loc, curr_time, visited_mask)
    if curr_count + possible_more <= best_count:
        return

    # Build candidates (feasible next)
    candidates = []
    for i, p in enumerate(people):
        if (visited_mask >> i) & 1:
            continue
        travel = travel_time(curr_loc, p["location"])
        arrive = curr_time + travel
        start = max(arrive, p["start_min"])
        end = start + p["duration"]
        if end <= p["end_min"]:
            # Heuristic key: earliest end, then shortest slack, then shortest travel
            slack = p["end_min"] - (start + p["duration"])
            candidates.append((p, i, start, end, travel, slack))

    # Order candidates to explore promising ones first
    candidates.sort(key=lambda x: (x[3], x[5], x[4]))

    for p, idx, meet_start, meet_end, travel, slack in candidates:
        if full_found:
            return
        new_path = path + [{
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end),
        }]
        dfs(p["location"], meet_end, visited_mask | (1 << idx), new_path)

# Start DFS
dfs(start_location, start_time, 0, [])

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))