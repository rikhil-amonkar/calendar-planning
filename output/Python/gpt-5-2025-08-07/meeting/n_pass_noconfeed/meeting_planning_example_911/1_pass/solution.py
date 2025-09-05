# SOLUTION:
import json
from functools import lru_cache

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (minutes) between neighborhoods
TT = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21,
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26,
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5,
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21,
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22,
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9,
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17,
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23,
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9,
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9,
    },
}

# People constraints
people = [
    {"person": "Steven", "location": "North Beach", "start": "17:30", "end": "20:30", "min_minutes": 15},
    {"person": "Sarah", "location": "Golden Gate Park", "start": "17:00", "end": "19:15", "min_minutes": 75},
    {"person": "Brian", "location": "Embarcadero", "start": "14:15", "end": "16:00", "min_minutes": 105},
    {"person": "Stephanie", "location": "Haight-Ashbury", "start": "10:15", "end": "12:15", "min_minutes": 75},
    {"person": "Melissa", "location": "Richmond District", "start": "14:00", "end": "19:30", "min_minutes": 30},
    {"person": "Nancy", "location": "Nob Hill", "start": "8:15", "end": "12:45", "min_minutes": 90},
    {"person": "David", "location": "Marina District", "start": "11:15", "end": "13:15", "min_minutes": 120},
    {"person": "James", "location": "Presidio", "start": "15:00", "end": "18:15", "min_minutes": 120},
    {"person": "Elizabeth", "location": "Union Square", "start": "11:30", "end": "21:00", "min_minutes": 60},
    {"person": "Robert", "location": "Financial District", "start": "13:15", "end": "15:15", "min_minutes": 45},
]

# Convert time strings to minutes
for p in people:
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

start_location = "The Castro"
start_time = time_to_minutes("9:00")

N = len(people)

# Pre-sort indices by their window ends (helps heuristic)
indices = list(range(N))
indices.sort(key=lambda i: people[i]["end_min"])

best_solution = {
    "count": 0,
    "end_time": float('inf'),
    "path": []
}

# For pruning: compute max possible remaining count from a given bitmask
def remaining_count(met_mask):
    return N - bin(met_mask).count("1")

@lru_cache(maxsize=None)
def dfs(cur_loc, cur_time, met_mask):
    # Return best (count, end_time, path_list_of_entries)
    best_local = (0, cur_time, [])  # no more meetings
    already_met = bin(met_mask).count("1")

    # Upper bound pruning
    global best_solution
    if already_met + remaining_count(met_mask) < best_solution["count"]:
        return best_local

    # Order candidates by earliest feasible end time heuristic
    candidates = []
    for i in indices:
        if (met_mask >> i) & 1:
            continue
        person = people[i]
        loc = person["location"]
        travel = TT[cur_loc][loc]
        arrival = cur_time + travel
        start = max(arrival, person["start_min"])
        end = start + person["min_minutes"]
        if end <= person["end_min"]:
            candidates.append((end, start, i, arrival))
    candidates.sort(key=lambda x: (x[0], x[1]))

    for end, start, i, arrival in candidates:
        person = people[i]
        loc = person["location"]

        # Construct meeting entry
        entry = {
            "action": "meet",
            "location": loc,
            "person": person["person"],
            "start_time_min": start,
            "end_time_min": end,
        }

        res_count, res_end, res_path = dfs(loc, end, met_mask | (1 << i))
        res_count += 1
        # prefer higher count, then earlier end time
        candidate_path = [entry] + res_path
        if (res_count > best_local[0]) or (res_count == best_local[0] and res_end < best_local[1]):
            best_local = (res_count, res_end, candidate_path)
            # Update global for pruning
            if res_count > best_solution["count"] or (res_count == best_solution["count"] and res_end < best_solution["end_time"]):
                best_solution["count"] = res_count
                best_solution["end_time"] = res_end
                best_solution["path"] = candidate_path

    return best_local

# Run search
dfs(start_location, start_time, 0)

# Build final itinerary with formatted times
# Start from initial location and time, ensure travel accounted implicitly as we scheduled
itinerary = []
for e in best_solution["path"]:
    itinerary.append({
        "action": "meet",
        "location": e["location"],
        "person": e["person"],
        "start_time": minutes_to_time(e["start_time_min"]),
        "end_time": minutes_to_time(e["end_time_min"]),
    })

output = {"itinerary": itinerary}

print("SOLUTION:")
print(json.dumps(output, ensure_ascii=False, indent=2))