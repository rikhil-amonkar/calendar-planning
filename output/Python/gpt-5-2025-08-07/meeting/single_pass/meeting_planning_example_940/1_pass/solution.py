import json
from functools import lru_cache

def to_minutes(t):
    # t like '9:00' or '20:45' (24h, no leading zero required)
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes)
travel = {
    "Union Square": {
        "Mission District": 14, "Fisherman's Wharf": 15, "Russian Hill": 13, "Marina District": 18,
        "North Beach": 10, "Chinatown": 7, "Pacific Heights": 15, "The Castro": 17, "Nob Hill": 9, "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15, "Fisherman's Wharf": 22, "Russian Hill": 15, "Marina District": 19,
        "North Beach": 17, "Chinatown": 16, "Pacific Heights": 16, "The Castro": 7, "Nob Hill": 12, "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "Mission District": 22, "Russian Hill": 7, "Marina District": 9,
        "North Beach": 6, "Chinatown": 12, "Pacific Heights": 12, "The Castro": 27, "Nob Hill": 11, "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10, "Mission District": 16, "Fisherman's Wharf": 7, "Marina District": 7,
        "North Beach": 5, "Chinatown": 9, "Pacific Heights": 7, "The Castro": 21, "Nob Hill": 5, "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16, "Mission District": 20, "Fisherman's Wharf": 10, "Russian Hill": 8,
        "North Beach": 11, "Chinatown": 15, "Pacific Heights": 7, "The Castro": 22, "Nob Hill": 12, "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7, "Mission District": 18, "Fisherman's Wharf": 5, "Russian Hill": 4,
        "Marina District": 9, "Chinatown": 6, "Pacific Heights": 8, "The Castro": 23, "Nob Hill": 7, "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7, "Mission District": 17, "Fisherman's Wharf": 8, "Russian Hill": 7,
        "Marina District": 12, "North Beach": 3, "Pacific Heights": 10, "The Castro": 22, "Nob Hill": 9, "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12, "Mission District": 15, "Fisherman's Wharf": 13, "Russian Hill": 7,
        "Marina District": 6, "North Beach": 9, "Chinatown": 11, "The Castro": 16, "Nob Hill": 8, "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19, "Mission District": 7, "Fisherman's Wharf": 24, "Russian Hill": 18,
        "Marina District": 21, "North Beach": 20, "Chinatown": 22, "Pacific Heights": 16, "Nob Hill": 16, "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7, "Mission District": 13, "Fisherman's Wharf": 10, "Russian Hill": 5,
        "Marina District": 11, "North Beach": 8, "Chinatown": 6, "Pacific Heights": 8, "The Castro": 17, "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30, "Mission District": 25, "Fisherman's Wharf": 29, "Russian Hill": 24,
        "Marina District": 21, "North Beach": 28, "Chinatown": 30, "Pacific Heights": 21, "The Castro": 17, "Nob Hill": 27
    }
}
# Add zero self-travel
for a in list(travel.keys()):
    travel[a][a] = 0

# Participants (24h times)
people = [
    {"name": "Kevin", "location": "Mission District", "start": to_minutes("20:45"), "end": to_minutes("21:45"), "min": 60},
    {"name": "Mark", "location": "Fisherman's Wharf", "start": to_minutes("17:15"), "end": to_minutes("20:00"), "min": 90},
    {"name": "Jessica", "location": "Russian Hill", "start": to_minutes("9:00"), "end": to_minutes("15:00"), "min": 120},
    {"name": "Jason", "location": "Marina District", "start": to_minutes("15:15"), "end": to_minutes("21:45"), "min": 120},
    {"name": "John", "location": "North Beach", "start": to_minutes("9:45"), "end": to_minutes("18:00"), "min": 15},
    {"name": "Karen", "location": "Chinatown", "start": to_minutes("16:45"), "end": to_minutes("19:00"), "min": 75},
    {"name": "Sarah", "location": "Pacific Heights", "start": to_minutes("17:30"), "end": to_minutes("18:15"), "min": 45},
    {"name": "Amanda", "location": "The Castro", "start": to_minutes("20:00"), "end": to_minutes("21:15"), "min": 60},
    {"name": "Nancy", "location": "Nob Hill", "start": to_minutes("9:45"), "end": to_minutes("13:00"), "min": 45},
    {"name": "Rebecca", "location": "Sunset District", "start": to_minutes("8:45"), "end": to_minutes("15:00"), "min": 75},
]

# Heuristic ordering: sort by window end time (earlier deadlines first)
people_order = sorted(range(len(people)), key=lambda i: (people[i]["end"], people[i]["start"]))
people = [people[i] for i in people_order]

start_location = "Union Square"
start_time = to_minutes("9:00")

# Greedy baseline to seed best
def greedy_plan():
    current_loc = start_location
    current_time = start_time
    remaining = set(range(len(people)))
    plan = []
    while True:
        candidates = []
        for i in list(remaining):
            p = people[i]
            arr = current_time + travel[current_loc][p["location"]]
            st = max(arr, p["start"])
            en = st + p["min"]
            if en <= p["end"]:
                candidates.append((en, st, i))
        if not candidates:
            break
        candidates.sort()  # earliest finish first
        _, st, i = candidates[0]
        p = people[i]
        en = st + p["min"]
        plan.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": st,
            "end_time": en
        })
        current_loc = p["location"]
        current_time = en
        remaining.remove(i)
    return plan

best_plan = greedy_plan()
best_count = len(best_plan)
best_total_minutes = sum(item["end_time"] - item["start_time"] for item in best_plan)

# DFS with pruning
from functools import lru_cache

@lru_cache(maxsize=None)
def bound_count(current_loc, current_time, remaining_tuple):
    # Upper bound: count how many meetings are individually feasible from current state (greedy optimistic)
    remaining = list(remaining_tuple)
    feasible = 0
    for i in remaining:
        p = people[i]
        arr = current_time + travel[current_loc][p["location"]]
        st = max(arr, p["start"])
        en = st + p["min"]
        if en <= p["end"]:
            feasible += 1
    return feasible

def dfs(current_loc, current_time, remaining_set, current_plan):
    global best_plan, best_count, best_total_minutes

    remaining_tuple = tuple(sorted(remaining_set))
    ub = len(current_plan) + bound_count(current_loc, current_time, remaining_tuple)
    if ub < best_count:
        return

    # Generate feasible next candidates
    candidates = []
    for i in remaining_set:
        p = people[i]
        arr = current_time + travel[current_loc][p["location"]]
        st = max(arr, p["start"])
        en = st + p["min"]
        if en <= p["end"]:
            # sort by earliest finish to branch promising paths first
            candidates.append((en, st, i))
    candidates.sort()

    improved = False
    for en, st, i in candidates:
        p = people[i]
        next_plan = current_plan + [{
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": st,
            "end_time": en
        }]
        next_remaining = set(remaining_set)
        next_remaining.remove(i)
        dfs(p["location"], en, next_remaining, next_plan)
        improved = True

    # If no candidates or end of branch, evaluate current plan
    if not improved:
        cnt = len(current_plan)
        tot = sum(item["end_time"] - item["start_time"] for item in current_plan)
        # Tie-breakers: maximize count, then total meeting minutes, then finish earlier
        finish_time = current_plan[-1]["end_time"] if current_plan else current_time
        best_finish_time = best_plan[-1]["end_time"] if best_plan else start_time
        if (cnt > best_count) or \
           (cnt == best_count and tot > best_total_minutes) or \
           (cnt == best_count and tot == best_total_minutes and finish_time < best_finish_time):
            best_plan = current_plan
            best_count = cnt
            best_total_minutes = tot

# Run DFS
remaining_all = set(range(len(people)))
dfs(start_location, start_time, remaining_all, [])

# Convert internal minute times to strings
output_plan = []
for item in best_plan:
    output_plan.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": to_str(item["start_time"]),
        "end_time": to_str(item["end_time"])
    })

result = {"itinerary": output_plan}
print(json.dumps(result, ensure_ascii=False))