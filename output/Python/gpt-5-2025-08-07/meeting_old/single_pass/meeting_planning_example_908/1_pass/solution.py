import json

def minutes(h, m):
    return h * 60 + m

def time_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (directed) in minutes
travel_list = [
    ("Financial District", "Fisherman's Wharf", 10),
    ("Financial District", "Presidio", 22),
    ("Financial District", "Bayview", 19),
    ("Financial District", "Haight-Ashbury", 19),
    ("Financial District", "Russian Hill", 11),
    ("Financial District", "The Castro", 20),
    ("Financial District", "Marina District", 15),
    ("Financial District", "Richmond District", 21),
    ("Financial District", "Union Square", 9),
    ("Financial District", "Sunset District", 30),

    ("Fisherman's Wharf", "Financial District", 11),
    ("Fisherman's Wharf", "Presidio", 17),
    ("Fisherman's Wharf", "Bayview", 26),
    ("Fisherman's Wharf", "Haight-Ashbury", 22),
    ("Fisherman's Wharf", "Russian Hill", 7),
    ("Fisherman's Wharf", "The Castro", 27),
    ("Fisherman's Wharf", "Marina District", 9),
    ("Fisherman's Wharf", "Richmond District", 18),
    ("Fisherman's Wharf", "Union Square", 13),
    ("Fisherman's Wharf", "Sunset District", 27),

    ("Presidio", "Financial District", 23),
    ("Presidio", "Fisherman's Wharf", 19),
    ("Presidio", "Bayview", 31),
    ("Presidio", "Haight-Ashbury", 15),
    ("Presidio", "Russian Hill", 14),
    ("Presidio", "The Castro", 21),
    ("Presidio", "Marina District", 11),
    ("Presidio", "Richmond District", 7),
    ("Presidio", "Union Square", 22),
    ("Presidio", "Sunset District", 15),

    ("Bayview", "Financial District", 19),
    ("Bayview", "Fisherman's Wharf", 25),
    ("Bayview", "Presidio", 32),
    ("Bayview", "Haight-Ashbury", 19),
    ("Bayview", "Russian Hill", 23),
    ("Bayview", "The Castro", 19),
    ("Bayview", "Marina District", 27),
    ("Bayview", "Richmond District", 25),
    ("Bayview", "Union Square", 18),
    ("Bayview", "Sunset District", 23),

    ("Haight-Ashbury", "Financial District", 21),
    ("Haight-Ashbury", "Fisherman's Wharf", 23),
    ("Haight-Ashbury", "Presidio", 15),
    ("Haight-Ashbury", "Bayview", 18),
    ("Haight-Ashbury", "Russian Hill", 17),
    ("Haight-Ashbury", "The Castro", 6),
    ("Haight-Ashbury", "Marina District", 17),
    ("Haight-Ashbury", "Richmond District", 10),
    ("Haight-Ashbury", "Union Square", 19),
    ("Haight-Ashbury", "Sunset District", 15),

    ("Russian Hill", "Financial District", 11),
    ("Russian Hill", "Fisherman's Wharf", 7),
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "Bayview", 23),
    ("Russian Hill", "Haight-Ashbury", 17),
    ("Russian Hill", "The Castro", 21),
    ("Russian Hill", "Marina District", 7),
    ("Russian Hill", "Richmond District", 14),
    ("Russian Hill", "Union Square", 10),
    ("Russian Hill", "Sunset District", 23),

    ("The Castro", "Financial District", 21),
    ("The Castro", "Fisherman's Wharf", 24),
    ("The Castro", "Presidio", 20),
    ("The Castro", "Bayview", 19),
    ("The Castro", "Haight-Ashbury", 6),
    ("The Castro", "Russian Hill", 18),
    ("The Castro", "Marina District", 21),
    ("The Castro", "Richmond District", 16),
    ("The Castro", "Union Square", 19),
    ("The Castro", "Sunset District", 17),

    ("Marina District", "Financial District", 17),
    ("Marina District", "Fisherman's Wharf", 10),
    ("Marina District", "Presidio", 10),
    ("Marina District", "Bayview", 27),
    ("Marina District", "Haight-Ashbury", 16),
    ("Marina District", "Russian Hill", 8),
    ("Marina District", "The Castro", 22),
    ("Marina District", "Richmond District", 11),
    ("Marina District", "Union Square", 16),
    ("Marina District", "Sunset District", 19),

    ("Richmond District", "Financial District", 22),
    ("Richmond District", "Fisherman's Wharf", 18),
    ("Richmond District", "Presidio", 7),
    ("Richmond District", "Bayview", 27),
    ("Richmond District", "Haight-Ashbury", 10),
    ("Richmond District", "Russian Hill", 13),
    ("Richmond District", "The Castro", 16),
    ("Richmond District", "Marina District", 9),
    ("Richmond District", "Union Square", 21),
    ("Richmond District", "Sunset District", 11),

    ("Union Square", "Financial District", 9),
    ("Union Square", "Fisherman's Wharf", 15),
    ("Union Square", "Presidio", 24),
    ("Union Square", "Bayview", 15),
    ("Union Square", "Haight-Ashbury", 18),
    ("Union Square", "Russian Hill", 13),
    ("Union Square", "The Castro", 17),
    ("Union Square", "Marina District", 18),
    ("Union Square", "Richmond District", 20),
    ("Union Square", "Sunset District", 27),

    ("Sunset District", "Financial District", 30),
    ("Sunset District", "Fisherman's Wharf", 29),
    ("Sunset District", "Presidio", 16),
    ("Sunset District", "Bayview", 22),
    ("Sunset District", "Haight-Ashbury", 15),
    ("Sunset District", "Russian Hill", 24),
    ("Sunset District", "The Castro", 17),
    ("Sunset District", "Marina District", 21),
    ("Sunset District", "Richmond District", 12),
    ("Sunset District", "Union Square", 30),
]

travel = {}
for a, b, t in travel_list:
    travel.setdefault(a, {})[b] = t

# Participants and constraints
friends = [
    {"name": "Mark", "location": "Fisherman's Wharf", "start": minutes(8,15), "end": minutes(10,0), "duration": 30},
    {"name": "Stephanie", "location": "Presidio", "start": minutes(12,15), "end": minutes(15,0), "duration": 75},
    {"name": "Betty", "location": "Bayview", "start": minutes(7,15), "end": minutes(20,30), "duration": 15},
    {"name": "Lisa", "location": "Haight-Ashbury", "start": minutes(15,30), "end": minutes(18,30), "duration": 45},
    {"name": "William", "location": "Russian Hill", "start": minutes(18,45), "end": minutes(20,0), "duration": 60},
    {"name": "Brian", "location": "The Castro", "start": minutes(9,15), "end": minutes(13,15), "duration": 30},
    {"name": "Joseph", "location": "Marina District", "start": minutes(10,45), "end": minutes(15,0), "duration": 90},
    {"name": "Ashley", "location": "Richmond District", "start": minutes(9,45), "end": minutes(11,15), "duration": 45},
    {"name": "Patricia", "location": "Union Square", "start": minutes(16,30), "end": minutes(20,0), "duration": 120},
    {"name": "Karen", "location": "Sunset District", "start": minutes(16,30), "end": minutes(22,0), "duration": 105},
]

start_location = "Financial District"
start_time = minutes(9, 0)

# Map friend to index for bitmasking
name_to_idx = {f["name"]: i for i, f in enumerate(friends)}

def earliest_meeting(cur_loc, cur_time, friend):
    t_travel = travel[cur_loc][friend["location"]]
    arrival = cur_time + t_travel
    start = max(arrival, friend["start"])
    end = start + friend["duration"]
    if end <= friend["end"]:
        return (start, end)
    return None

def greedy_schedule(cur_loc, cur_time, remaining_names):
    remaining = {name: friends[name_to_idx[name]] for name in remaining_names}
    path = []
    while True:
        candidates = []
        for nm, fr in remaining.items():
            mt = earliest_meeting(cur_loc, cur_time, fr)
            if mt:
                s, e = mt
                candidates.append((e, s, nm, fr))
        if not candidates:
            break
        candidates.sort()  # earliest end first
        e, s, nm, fr = candidates[0]
        path.append({"action": "meet", "location": fr["location"], "person": nm, "start": s, "end": e})
        cur_loc = fr["location"]
        cur_time = e
        del remaining[nm]
    return path

# DFS with pruning
best_solution = {"count": 0, "end_time": float('inf'), "path": []}

def search(cur_loc, cur_time, remaining_bitmask, path):
    global best_solution
    # Upper bound pruning: current count + remaining potential
    remaining_count = bin(remaining_bitmask).count("1")
    current_count = len(path)
    if current_count + remaining_count < best_solution["count"]:
        return
    # A quick optimistic feasible count check (count friends that are still potentially meetable from now)
    # Not a strict bound but can help prune slightly
    potential = 0
    for i, fr in enumerate(friends):
        if (remaining_bitmask >> i) & 1:
            mt = earliest_meeting(cur_loc, cur_time, fr)
            if mt:
                potential += 1
    if current_count + potential < best_solution["count"]:
        return

    # Try to extend
    candidates = []
    for i, fr in enumerate(friends):
        if not ((remaining_bitmask >> i) & 1):
            continue
        mt = earliest_meeting(cur_loc, cur_time, fr)
        if mt:
            s, e = mt
            candidates.append((e, s, i, fr))
    # If no candidates, update best
    if not candidates:
        if current_count > best_solution["count"] or (current_count == best_solution["count"] and (path[-1]["end"] if path else cur_time) < best_solution["end_time"]):
            best_solution["count"] = current_count
            best_solution["end_time"] = path[-1]["end"] if path else cur_time
            best_solution["path"] = list(path)
        return

    # Heuristic ordering: earliest end time first
    candidates.sort()

    # Explore candidates
    for e, s, idx, fr in candidates:
        # Add this meeting
        new_path = path + [{"action": "meet", "location": fr["location"], "person": fr["name"], "start": s, "end": e}]
        new_mask = remaining_bitmask & ~(1 << idx)
        search(fr["location"], e, new_mask, new_path)

# Initialize with a greedy to set a strong baseline
all_names = [f["name"] for f in friends]
greedy_path = greedy_schedule(start_location, start_time, all_names)
best_solution["count"] = len(greedy_path)
best_solution["end_time"] = greedy_path[-1]["end"] if greedy_path else start_time
best_solution["path"] = greedy_path

# Start DFS
remaining_mask = (1 << len(friends)) - 1
search(start_location, start_time, remaining_mask, [])

# Build output
output_itinerary = []
for item in best_solution["path"]:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": time_to_str(item["start"]),
        "end_time": time_to_str(item["end"]),
    })

print(json.dumps({"itinerary": output_itinerary}, ensure_ascii=False))