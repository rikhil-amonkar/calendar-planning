import itertools, json

def time_to_minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Financial District"
start_time = time_to_minutes(9, 0)

# Directed travel times (in minutes)
travel = {
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 23,
    ("Financial District", "Golden Gate Park"): 23,

    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,

    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Golden Gate Park"): 11,

    ("North Beach", "Financial District"): 8,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,

    ("The Castro", "Financial District"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,

    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "The Castro"): 13,
}

# People constraints
people = [
    {
        "name": "Ronald",
        "location": "Russian Hill",
        "window_start": time_to_minutes(13, 45),
        "window_end": time_to_minutes(17, 15),
        "min_duration": 105
    },
    {
        "name": "Patricia",
        "location": "Sunset District",
        "window_start": time_to_minutes(9, 15),
        "window_end": time_to_minutes(22, 0),
        "min_duration": 60
    },
    {
        "name": "Laura",
        "location": "North Beach",
        "window_start": time_to_minutes(12, 30),
        "window_end": time_to_minutes(12, 45),
        "min_duration": 15
    },
    {
        "name": "Emily",
        "location": "The Castro",
        "window_start": time_to_minutes(16, 15),
        "window_end": time_to_minutes(18, 30),
        "min_duration": 60
    },
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "window_start": time_to_minutes(15, 0),
        "window_end": time_to_minutes(16, 30),
        "min_duration": 60
    },
]

def feasible_schedule(order):
    time = start_time
    loc = start_location
    itinerary = []
    total_wait = 0
    total_travel = 0

    for person in order:
        key = (loc, person["location"])
        if key not in travel:
            return None  # cannot travel
        t_travel = travel[key]
        arrival = time + t_travel
        total_travel += t_travel

        start_meet = max(arrival, person["window_start"])
        end_meet = start_meet + person["min_duration"]

        # Waiting occurs if we arrive before we can start
        wait = max(0, start_meet - arrival)
        total_wait += wait

        if end_meet > person["window_end"]:
            return None  # violates availability

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start": start_meet,
            "end": end_meet
        })
        time = end_meet
        loc = person["location"]

    return {
        "itinerary": itinerary,
        "end_time": time,
        "wait": total_wait,
        "travel": total_travel
    }

# Search over all subsets and permutations to maximize number of friends met
best = None

# Generate all non-empty subsets
for r in range(1, len(people) + 1):
    for subset in itertools.combinations(people, r):
        # Try all permutations (orders)
        for perm in itertools.permutations(subset):
            result = feasible_schedule(perm)
            if result is None:
                continue
            # Scoring: maximize count, then minimize end_time, then wait, then travel
            score = (
                len(perm),                       # higher is better
                -result["end_time"],             # smaller end_time is better -> negate to maximize
                -result["wait"],                 # smaller wait better
                -result["travel"]                # smaller travel better
            )
            if best is None or score > best["score"]:
                best = {
                    "score": score,
                    "result": result
                }

# Build output JSON
output = {"itinerary": []}
if best is not None:
    for item in best["result"]["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start"]),
            "end_time": minutes_to_str(item["end"])
        })

print(json.dumps(output))