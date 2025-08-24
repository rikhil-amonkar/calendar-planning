import json

def parse_time_12h(s):
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        time_part = s[:-2]
    else:
        time_part = s
        ampm = None
    time_part = time_part.strip()
    if ":" in time_part:
        h, m = time_part.split(":")
        h = int(h)
        m = int(m)
    else:
        h = int(time_part)
        m = 0
    if ampm == "AM":
        if h == 12:
            h = 0
    elif ampm == "PM":
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables

locations = [
    "The Castro",
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Richmond District",
    "Nob Hill",
    "Marina District",
    "Presidio",
    "Union Square",
    "Financial District",
]

# Travel times (directed, minutes)
T = {
    "The Castro": {
        "North Beach": 20, "Golden Gate Park": 11, "Embarcadero": 22, "Haight-Ashbury": 6,
        "Richmond District": 16, "Nob Hill": 16, "Marina District": 21, "Presidio": 20,
        "Union Square": 19, "Financial District": 21,
    },
    "North Beach": {
        "The Castro": 23, "Golden Gate Park": 22, "Embarcadero": 6, "Haight-Ashbury": 18,
        "Richmond District": 18, "Nob Hill": 7, "Marina District": 9, "Presidio": 17,
        "Union Square": 7, "Financial District": 8,
    },
    "Golden Gate Park": {
        "The Castro": 13, "North Beach": 23, "Embarcadero": 25, "Haight-Ashbury": 7,
        "Richmond District": 7, "Nob Hill": 20, "Marina District": 16, "Presidio": 11,
        "Union Square": 22, "Financial District": 26,
    },
    "Embarcadero": {
        "The Castro": 25, "North Beach": 5, "Golden Gate Park": 25, "Haight-Ashbury": 21,
        "Richmond District": 21, "Nob Hill": 10, "Marina District": 12, "Presidio": 20,
        "Union Square": 10, "Financial District": 5,
    },
    "Haight-Ashbury": {
        "The Castro": 6, "North Beach": 19, "Golden Gate Park": 7, "Embarcadero": 20,
        "Richmond District": 10, "Nob Hill": 15, "Marina District": 17, "Presidio": 15,
        "Union Square": 19, "Financial District": 21,
    },
    "Richmond District": {
        "The Castro": 16, "North Beach": 17, "Golden Gate Park": 9, "Embarcadero": 19,
        "Haight-Ashbury": 10, "Nob Hill": 17, "Marina District": 9, "Presidio": 7,
        "Union Square": 21, "Financial District": 22,
    },
    "Nob Hill": {
        "The Castro": 17, "North Beach": 8, "Golden Gate Park": 17, "Embarcadero": 9,
        "Haight-Ashbury": 13, "Richmond District": 14, "Marina District": 11, "Presidio": 17,
        "Union Square": 7, "Financial District": 9,
    },
    "Marina District": {
        "The Castro": 22, "North Beach": 11, "Golden Gate Park": 18, "Embarcadero": 14,
        "Haight-Ashbury": 16, "Richmond District": 11, "Nob Hill": 12, "Presidio": 10,
        "Union Square": 16, "Financial District": 17,
    },
    "Presidio": {
        "The Castro": 21, "North Beach": 18, "Golden Gate Park": 12, "Embarcadero": 20,
        "Haight-Ashbury": 15, "Richmond District": 7, "Nob Hill": 18, "Marina District": 11,
        "Union Square": 22, "Financial District": 23,
    },
    "Union Square": {
        "The Castro": 17, "North Beach": 10, "Golden Gate Park": 22, "Embarcadero": 11,
        "Haight-Ashbury": 18, "Richmond District": 20, "Nob Hill": 9, "Marina District": 18,
        "Presidio": 24, "Financial District": 9,
    },
    "Financial District": {
        "The Castro": 20, "North Beach": 7, "Golden Gate Park": 23, "Embarcadero": 4,
        "Haight-Ashbury": 19, "Richmond District": 21, "Nob Hill": 8, "Marina District": 15,
        "Presidio": 22, "Union Square": 9,
    },
}

# Ensure zero self-travel times
for a in locations:
    if a not in T:
        T[a] = {}
    T[a][a] = 0
    for b in locations:
        if b not in T[a]:
            # If a->b not explicitly provided, try to be conservative: use max of provided symmetric pair if exists
            # but since data is mostly complete, we'll just set a big number to avoid infeasible jumps
            T[a][b] = 9999

start_location = "The Castro"
start_time = parse_time_12h("9:00AM")

meetings = [
    {"person": "Steven", "location": "North Beach", "start": parse_time_12h("5:30PM"), "end": parse_time_12h("8:30PM"), "min_dur": 15},
    {"person": "Sarah", "location": "Golden Gate Park", "start": parse_time_12h("5:00PM"), "end": parse_time_12h("7:15PM"), "min_dur": 75},
    {"person": "Brian", "location": "Embarcadero", "start": parse_time_12h("2:15PM"), "end": parse_time_12h("4:00PM"), "min_dur": 105},
    {"person": "Stephanie", "location": "Haight-Ashbury", "start": parse_time_12h("10:15AM"), "end": parse_time_12h("12:15PM"), "min_dur": 75},
    {"person": "Melissa", "location": "Richmond District", "start": parse_time_12h("2:00PM"), "end": parse_time_12h("7:30PM"), "min_dur": 30},
    {"person": "Nancy", "location": "Nob Hill", "start": parse_time_12h("8:15AM"), "end": parse_time_12h("12:45PM"), "min_dur": 90},
    {"person": "David", "location": "Marina District", "start": parse_time_12h("11:15AM"), "end": parse_time_12h("1:15PM"), "min_dur": 120},
    {"person": "James", "location": "Presidio", "start": parse_time_12h("3:00PM"), "end": parse_time_12h("6:15PM"), "min_dur": 120},
    {"person": "Elizabeth", "location": "Union Square", "start": parse_time_12h("11:30AM"), "end": parse_time_12h("9:00PM"), "min_dur": 60},
    {"person": "Robert", "location": "Financial District", "start": parse_time_12h("1:15PM"), "end": parse_time_12h("3:15PM"), "min_dur": 45},
]

# Assign indices
for i, m in enumerate(meetings):
    m["idx"] = i

# DFS with pruning to maximize number of meetings; tie-breakers: max total meeting minutes, earliest finish, minimal travel
N = len(meetings)

best_solution = {
    "count": -1,
    "total_meeting_minutes": -1,
    "end_time": 10**9,
    "total_travel": 10**9,
    "path": [],
}

# Precompute ordering heuristic: by window end time
order_indices = sorted(range(N), key=lambda i: meetings[i]["end"])

# Memoization: for (loc, time, visited_mask) keep earliest time seen; if we've been earlier or equal, prune
from functools import lru_cache

def search(current_loc, current_time, visited_mask, path, total_travel):
    global best_solution
    count = len(path)

    # Upper bound pruning by remaining people
    remaining_possible = N - bin(visited_mask).count("1")
    if count + remaining_possible < best_solution["count"]:
        return

    # Update best with current path
    total_meeting_minutes = sum(seg["end"] - seg["start"] for seg in path)
    if (count > best_solution["count"] or
        (count == best_solution["count"] and (total_meeting_minutes > best_solution["total_meeting_minutes"] or
         (total_meeting_minutes == best_solution["total_meeting_minutes"] and (current_time < best_solution["end_time"] or
          (current_time == best_solution["end_time"] and total_travel < best_solution["total_travel"])))))):
        best_solution = {
            "count": count,
            "total_meeting_minutes": total_meeting_minutes,
            "end_time": current_time,
            "total_travel": total_travel,
            "path": list(path),
        }

    state_key = (current_loc, current_time, visited_mask)
    if state_key in seen:
        prev_time, prev_count = seen[state_key]
        # If we've been here earlier or equal with same or more count, prune
        if current_time >= prev_time and count <= prev_count:
            return
        # Otherwise keep the better of the two records
        if current_time < prev_time or count > prev_count:
            seen[state_key] = (current_time, count)
    else:
        seen[state_key] = (current_time, count)

    # Generate feasible next meetings
    # Iterate in heuristic order: earlier window ends first
    for i in order_indices:
        if (visited_mask >> i) & 1:
            continue
        m = meetings[i]
        travel_time = T[current_loc][m["location"]]
        if travel_time >= 9999:
            continue  # unreachable
        arrival = current_time + travel_time
        # Earliest possible start considering waiting for window
        start = max(arrival, m["start"])
        end = start + m["min_dur"]
        if end <= m["end"]:
            # Feasible; schedule at earliest feasible start
            path.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start": start,
                "end": end,
            })
            search(m["location"], end, visited_mask | (1 << i), path, total_travel + travel_time)
            path.pop()
        else:
            # Not feasible; skip
            continue

# Initialize seen dict
seen = {}

search(start_location, start_time, 0, [], 0)

# Prepare output
itinerary = []
for seg in best_solution["path"]:
    itinerary.append({
        "action": "meet",
        "location": seg["location"],
        "person": seg["person"],
        "start_time": fmt_time(seg["start"]),
        "end_time": fmt_time(seg["end"]),
    })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))