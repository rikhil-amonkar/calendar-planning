import json
from itertools import permutations

def time_to_minutes(t):
    # t in 'H:MM' 24h or minutes integer
    if isinstance(t, int):
        return t
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes (directed)
travel = {
    "Mission District": {
        "Alamo Square": 11, "Presidio": 25, "Russian Hill": 15, "North Beach": 17,
        "Golden Gate Park": 17, "Richmond District": 20, "Embarcadero": 19,
        "Financial District": 15, "Marina District": 19
    },
    "Alamo Square": {
        "Mission District": 10, "Presidio": 17, "Russian Hill": 13, "North Beach": 15,
        "Golden Gate Park": 9, "Richmond District": 11, "Embarcadero": 16,
        "Financial District": 17, "Marina District": 15
    },
    "Presidio": {
        "Mission District": 26, "Alamo Square": 19, "Russian Hill": 14, "North Beach": 18,
        "Golden Gate Park": 12, "Richmond District": 7, "Embarcadero": 20,
        "Financial District": 23, "Marina District": 11
    },
    "Russian Hill": {
        "Mission District": 16, "Alamo Square": 15, "Presidio": 14, "North Beach": 5,
        "Golden Gate Park": 21, "Richmond District": 14, "Embarcadero": 8,
        "Financial District": 11, "Marina District": 7
    },
    "North Beach": {
        "Mission District": 18, "Alamo Square": 16, "Presidio": 17, "Russian Hill": 4,
        "Golden Gate Park": 22, "Richmond District": 18, "Embarcadero": 6,
        "Financial District": 8, "Marina District": 9
    },
    "Golden Gate Park": {
        "Mission District": 17, "Alamo Square": 9, "Presidio": 11, "Russian Hill": 19,
        "North Beach": 23, "Richmond District": 7, "Embarcadero": 25,
        "Financial District": 26, "Marina District": 16
    },
    "Richmond District": {
        "Mission District": 20, "Alamo Square": 13, "Presidio": 7, "Russian Hill": 13,
        "North Beach": 17, "Golden Gate Park": 9, "Embarcadero": 19,
        "Financial District": 22, "Marina District": 9
    },
    "Embarcadero": {
        "Mission District": 20, "Alamo Square": 19, "Presidio": 20, "Russian Hill": 8,
        "North Beach": 5, "Golden Gate Park": 25, "Richmond District": 21,
        "Financial District": 5, "Marina District": 12
    },
    "Financial District": {
        "Mission District": 17, "Alamo Square": 17, "Presidio": 22, "Russian Hill": 11,
        "North Beach": 7, "Golden Gate Park": 23, "Richmond District": 21,
        "Embarcadero": 4, "Marina District": 15
    },
    "Marina District": {
        "Mission District": 20, "Alamo Square": 15, "Presidio": 10, "Russian Hill": 8,
        "North Beach": 11, "Golden Gate Park": 18, "Richmond District": 11,
        "Embarcadero": 14, "Financial District": 17
    },
}

# Meeting constraints
friends = [
    {"person": "Laura", "location": "Alamo Square", "start": "14:30", "end": "16:15", "min_minutes": 75},
    {"person": "Brian", "location": "Presidio", "start": "10:15", "end": "17:00", "min_minutes": 30},
    {"person": "Karen", "location": "Russian Hill", "start": "18:00", "end": "20:15", "min_minutes": 90},
    {"person": "Stephanie", "location": "North Beach", "start": "10:15", "end": "16:00", "min_minutes": 75},
    {"person": "Helen", "location": "Golden Gate Park", "start": "11:30", "end": "21:45", "min_minutes": 120},
    {"person": "Sandra", "location": "Richmond District", "start": "8:00", "end": "15:15", "min_minutes": 30},
    {"person": "Mary", "location": "Embarcadero", "start": "16:45", "end": "18:45", "min_minutes": 120},
    {"person": "Deborah", "location": "Financial District", "start": "19:00", "end": "20:45", "min_minutes": 105},
    {"person": "Elizabeth", "location": "Marina District", "start": "8:30", "end": "13:15", "min_minutes": 105},
]

# Convert times to minutes
for f in friends:
    f["start_min"] = time_to_minutes(f["start"])
    f["end_min"] = time_to_minutes(f["end"])

start_location = "Mission District"
start_time_min = time_to_minutes("9:00")

# Build a quick lookup by name for later if needed
name_to_friend = {f["person"]: f for f in friends}

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Scoring: maximize (count, total_meet_minutes, -total_wait, -total_travel, -finish_time)
def score_of(schedule, total_travel, total_wait):
    count = len(schedule)
    total_meet = sum(item["end"] - item["start"] for item in schedule)
    finish = schedule[-1]["end"] if schedule else start_time_min
    return (count, total_meet, -total_wait, -total_travel, -finish)

best_result = {
    "schedule": [],
    "score": (-1, -1, 0, 0, 0),
    "total_travel": 0,
    "total_wait": 0
}

from functools import lru_cache

# Pre-calc a list of indices for iteration
friend_indices = list(range(len(friends)))

@lru_cache(maxsize=None)
def dfs(current_loc, current_time, met_mask):
    # Returns tuple: (score_tuple, schedule_list, total_travel, total_wait)
    best = (score_of([], 0, 0), [], 0, 0)

    # Try meeting each remaining friend next
    for i in friend_indices:
        if (met_mask >> i) & 1:
            continue  # already met
        f = friends[i]
        t_travel = get_travel(current_loc, f["location"])
        arrival = current_time + t_travel
        start_meet = max(arrival, f["start_min"])
        end_meet = start_meet + f["min_minutes"]
        if end_meet > f["end_min"]:
            continue  # infeasible

        wait = max(0, start_meet - arrival)

        # Recurse from the end of this meeting
        next_score, next_sched, next_travel, next_wait = dfs(
            f["location"], end_meet, met_mask | (1 << i)
        )

        # Prepend this meeting
        schedule_here = [{
            "action": "meet",
            "location": f["location"],
            "person": f["person"],
            "start": start_meet,
            "end": end_meet
        }] + next_sched

        total_travel_here = t_travel + next_travel
        total_wait_here = wait + next_wait
        score_here = score_of(schedule_here, total_travel_here, total_wait_here)

        # Choose best by score; if tie, use lexicographic of serialized schedule to stabilize
        if score_here > best[0]:
            best = (score_here, schedule_here, total_travel_here, total_wait_here)
        elif score_here == best[0]:
            # Tie-breaker stable ordering by names and times to ensure determinism
            key_a = [(s["person"], s["location"], s["start"], s["end"]) for s in schedule_here]
            key_b = [(s["person"], s["location"], s["start"], s["end"]) for s in best[1]]
            if key_a < key_b:
                best = (score_here, schedule_here, total_travel_here, total_wait_here)

    return best

best_score, best_schedule, best_travel, best_wait = dfs(start_location, start_time_min, 0)

# Convert times to strings for JSON output
output_itinerary = []
for item in best_schedule:
    output_itinerary.append({
        "action": item["action"],
        "location": item["location"],
        "person": item["person"],
        "start_time": minutes_to_time(item["start"]),
        "end_time": minutes_to_time(item["end"]),
    })

result = {"itinerary": output_itinerary}

print(json.dumps(result, ensure_ascii=False))