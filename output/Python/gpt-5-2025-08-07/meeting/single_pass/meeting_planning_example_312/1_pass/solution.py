import itertools
import json

# Helper: time conversion
def to_minutes(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def minutes_to_str(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Input variables: Locations and travel times (in minutes)
locations = [
    "Richmond District",
    "Sunset District",
    "Haight-Ashbury",
    "Mission District",
    "Golden Gate Park",
]

travel = {
    "Richmond District": {
        "Sunset District": 11,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Golden Gate Park": 9,
    },
    "Sunset District": {
        "Richmond District": 12,
        "Haight-Ashbury": 15,
        "Mission District": 24,
        "Golden Gate Park": 11,
    },
    "Haight-Ashbury": {
        "Richmond District": 10,
        "Sunset District": 15,
        "Mission District": 11,
        "Golden Gate Park": 7,
    },
    "Mission District": {
        "Richmond District": 20,
        "Sunset District": 24,
        "Haight-Ashbury": 12,
        "Golden Gate Park": 17,
    },
    "Golden Gate Park": {
        "Richmond District": 7,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Mission District": 17,
    },
}

# Starting conditions
start_location = "Richmond District"
start_time_str = "9:00"

# People and constraints
friends = [
    {
        "name": "Sarah",
        "location": "Sunset District",
        "window_start": "10:45",
        "window_end": "19:00",
        "min_minutes": 30,
    },
    {
        "name": "Richard",
        "location": "Haight-Ashbury",
        "window_start": "11:45",
        "window_end": "15:45",
        "min_minutes": 90,
    },
    {
        "name": "Elizabeth",
        "location": "Mission District",
        "window_start": "11:00",
        "window_end": "17:15",
        "min_minutes": 120,
    },
    {
        "name": "Michelle",
        "location": "Golden Gate Park",
        "window_start": "18:15",
        "window_end": "20:45",
        "min_minutes": 90,
    },
]

# Preprocess times into minutes
for f in friends:
    f["start_min"] = to_minutes(f["window_start"])
    f["end_min"] = to_minutes(f["window_end"])

start_time_min = to_minutes(start_time_str)

def simulate_sequence(seq):
    current_loc = start_location
    current_time = start_time_min
    itinerary = []
    total_travel = 0
    total_wait = 0

    for f in seq:
        # Travel time to friend's location
        t = travel[current_loc][f["location"]] if current_loc != f["location"] else 0
        arrival = current_time + t
        meet_start = max(arrival, f["start_min"])
        # Check feasibility: must fit minimum duration within availability
        if meet_start + f["min_minutes"] > f["end_min"]:
            return None  # infeasible sequence

        wait = max(0, meet_start - arrival)
        total_wait += wait
        total_travel += t
        meet_end = meet_start + f["min_minutes"]

        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time_min": meet_start,
            "end_time_min": meet_end,
        })

        current_time = meet_end
        current_loc = f["location"]

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "sequence_names": " > ".join([f["name"] for f in seq]),
    }

# Search over all subsets and permutations to maximize number of friends met
best = None
best_score = None
best_seq_names = None

n = len(friends)
# Iterate from largest subset size to smallest
for r in range(n, 0, -1):
    for subset in itertools.combinations(friends, r):
        for perm in itertools.permutations(subset):
            result = simulate_sequence(perm)
            if not result:
                continue
            # Objective: maximize number met, then minimize finish time,
            # then minimize total travel, then minimize total waiting,
            # then lexicographically smallest sequence of names for stability
            num_met = r
            finish_time = result["finish_time"]
            total_travel = result["total_travel"]
            total_wait = result["total_wait"]
            seq_names = result["sequence_names"]

            score = (num_met, -finish_time, -total_travel, -total_wait)
            if (best_score is None or
                score > best_score or
                (score == best_score and seq_names < best_seq_names)):
                best = result
                best_score = score
                best_seq_names = seq_names

# Build output JSON
output_itinerary = []
if best:
    for item in best["itinerary"]:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start_time_min"]),
            "end_time": minutes_to_str(item["end_time_min"]),
        })

result_json = {"itinerary": output_itinerary}
print(json.dumps(result_json, ensure_ascii=False))