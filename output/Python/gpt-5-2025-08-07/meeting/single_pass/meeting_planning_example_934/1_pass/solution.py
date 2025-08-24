import json
from functools import lru_cache

# -----------------------------
# Utility functions
# -----------------------------
def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# -----------------------------
# Travel times (minutes)
# -----------------------------
locations = [
    "Nob Hill",
    "Embarcadero",
    "The Castro",
    "Haight-Ashbury",
    "Union Square",
    "North Beach",
    "Pacific Heights",
    "Chinatown",
    "Golden Gate Park",
    "Marina District",
    "Russian Hill",
]

travel = {
    "Nob Hill": {
        "Embarcadero": 9,
        "The Castro": 17,
        "Haight-Ashbury": 13,
        "Union Square": 7,
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Golden Gate Park": 17,
        "Marina District": 11,
        "Russian Hill": 5,
    },
    "Embarcadero": {
        "Nob Hill": 10,
        "The Castro": 25,
        "Haight-Ashbury": 21,
        "Union Square": 10,
        "North Beach": 5,
        "Pacific Heights": 11,
        "Chinatown": 7,
        "Golden Gate Park": 25,
        "Marina District": 12,
        "Russian Hill": 8,
    },
    "The Castro": {
        "Nob Hill": 16,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Union Square": 19,
        "North Beach": 20,
        "Pacific Heights": 16,
        "Chinatown": 22,
        "Golden Gate Park": 11,
        "Marina District": 21,
        "Russian Hill": 18,
    },
    "Haight-Ashbury": {
        "Nob Hill": 15,
        "Embarcadero": 20,
        "The Castro": 6,
        "Union Square": 19,
        "North Beach": 19,
        "Pacific Heights": 12,
        "Chinatown": 19,
        "Golden Gate Park": 7,
        "Marina District": 17,
        "Russian Hill": 17,
    },
    "Union Square": {
        "Nob Hill": 9,
        "Embarcadero": 11,
        "The Castro": 17,
        "Haight-Ashbury": 18,
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Golden Gate Park": 22,
        "Marina District": 18,
        "Russian Hill": 13,
    },
    "North Beach": {
        "Nob Hill": 7,
        "Embarcadero": 6,
        "The Castro": 23,
        "Haight-Ashbury": 18,
        "Union Square": 7,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Golden Gate Park": 22,
        "Marina District": 9,
        "Russian Hill": 4,
    },
    "Pacific Heights": {
        "Nob Hill": 8,
        "Embarcadero": 10,
        "The Castro": 16,
        "Haight-Ashbury": 11,
        "Union Square": 12,
        "North Beach": 9,
        "Chinatown": 11,
        "Golden Gate Park": 15,
        "Marina District": 6,
        "Russian Hill": 7,
    },
    "Chinatown": {
        "Nob Hill": 9,
        "Embarcadero": 5,
        "The Castro": 22,
        "Haight-Ashbury": 19,
        "Union Square": 7,
        "North Beach": 3,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Marina District": 12,
        "Russian Hill": 7,
    },
    "Golden Gate Park": {
        "Nob Hill": 20,
        "Embarcadero": 25,
        "The Castro": 13,
        "Haight-Ashbury": 7,
        "Union Square": 22,
        "North Beach": 23,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Marina District": 16,
        "Russian Hill": 19,
    },
    "Marina District": {
        "Nob Hill": 12,
        "Embarcadero": 14,
        "The Castro": 22,
        "Haight-Ashbury": 16,
        "Union Square": 16,
        "North Beach": 11,
        "Pacific Heights": 7,
        "Chinatown": 15,
        "Golden Gate Park": 18,
        "Russian Hill": 8,
    },
    "Russian Hill": {
        "Nob Hill": 5,
        "Embarcadero": 8,
        "The Castro": 21,
        "Haight-Ashbury": 17,
        "Union Square": 10,
        "North Beach": 5,
        "Pacific Heights": 7,
        "Chinatown": 9,
        "Golden Gate Park": 21,
        "Marina District": 7,
    },
}

# Precompute index mapping for locations for performance
loc_to_idx = {loc: i for i, loc in enumerate(locations)}
idx_to_loc = {i: loc for loc, i in loc_to_idx.items()}

# Build matrix for quick access
nloc = len(locations)
travel_mat = [[0] * nloc for _ in range(nloc)]
for src, dests in travel.items():
    s = loc_to_idx[src]
    for dst, mins in dests.items():
        d = loc_to_idx[dst]
        travel_mat[s][d] = mins

# -----------------------------
# People constraints
# -----------------------------
people = [
    {"name": "Mary", "location": "Embarcadero", "start": "20:00", "end": "21:15", "min_dur": 75},
    {"name": "Kenneth", "location": "The Castro", "start": "11:15", "end": "19:15", "min_dur": 30},
    {"name": "Joseph", "location": "Haight-Ashbury", "start": "20:00", "end": "22:00", "min_dur": 120},
    {"name": "Sarah", "location": "Union Square", "start": "11:45", "end": "14:30", "min_dur": 90},
    {"name": "Thomas", "location": "North Beach", "start": "19:15", "end": "19:45", "min_dur": 15},
    {"name": "Daniel", "location": "Pacific Heights", "start": "13:45", "end": "20:30", "min_dur": 15},
    {"name": "Richard", "location": "Chinatown", "start": "8:00", "end": "18:45", "min_dur": 30},
    {"name": "Mark", "location": "Golden Gate Park", "start": "17:30", "end": "21:30", "min_dur": 120},
    {"name": "David", "location": "Marina District", "start": "20:00", "end": "21:00", "min_dur": 60},
    {"name": "Karen", "location": "Russian Hill", "start": "13:15", "end": "18:30", "min_dur": 120},
]

# Convert people times and map to indices
for p in people:
    p["start_min"] = to_minutes(p["start"])
    p["end_min"] = to_minutes(p["end"])
    p["loc_idx"] = loc_to_idx[p["location"]]

n_people = len(people)
name_to_idx = {p["name"]: i for i, p in enumerate(people)}

# -----------------------------
# Search for optimal schedule
# -----------------------------
start_location = "Nob Hill"
start_time = to_minutes("9:00")
start_loc_idx = loc_to_idx[start_location]

@lru_cache(maxsize=None)
def dfs(current_loc_idx, current_time, remaining_mask):
    # Returns tuple: (count, total_meeting_minutes, neg_total_travel_minutes, itinerary_tuple)
    best = (0, 0, 0, tuple())
    if remaining_mask == 0:
        return best

    for i in range(n_people):
        if not (remaining_mask & (1 << i)):
            continue
        p = people[i]
        travel_time = travel_mat[current_loc_idx][p["loc_idx"]]
        arrival = current_time + travel_time
        start = max(arrival, p["start_min"])
        end = start + p["min_dur"]
        if end <= p["end_min"]:
            next_mask = remaining_mask & ~(1 << i)
            child = dfs(p["loc_idx"], end, next_mask)
            cand_score = (
                1 + child[0],                          # count
                p["min_dur"] + child[1],               # total meeting minutes
                (-travel_time) + child[2],             # negative total travel (to minimize travel)
                ((i, start, end),) + child[3],         # itinerary (prepend current meeting)
            )
            # Choose best lexicographically
            if cand_score[:3] > best[:3]:
                best = cand_score
            elif cand_score[:3] == best[:3]:
                # As a tertiary tie-breaker, prefer earlier finishing time
                if child[3]:
                    child_end_time = child[3][-1][2]
                else:
                    child_end_time = end
                if best[3]:
                    best_end_time = best[3][-1][2]
                else:
                    best_end_time = end
                if child_end_time < best_end_time:
                    best = cand_score
    return best

full_mask = (1 << n_people) - 1
count, total_meeting_minutes, neg_total_travel, itinerary = dfs(start_loc_idx, start_time, full_mask)

# The itinerary returned is in the order of meetings scheduled (prepended), already chronological by construction
# Build JSON output
output = {"itinerary": []}
for (pi, smin, emin) in itinerary:
    p = people[pi]
    output["itinerary"].append({
        "action": "meet",
        "location": p["location"],
        "person": p["name"],
        "start_time": fmt_minutes(smin),
        "end_time": fmt_minutes(emin),
    })

print(json.dumps(output, ensure_ascii=False, indent=2))