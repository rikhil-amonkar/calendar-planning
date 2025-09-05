# SOLUTION:
import json
import itertools

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Union Square"
start_time_str = "9:00"
start_time = to_minutes(start_time_str)

# Travel times (in minutes), directional
travel = {
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,

    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "The Castro"): 13,

    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,

    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,

    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "The Castro"): 22,

    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Chinatown"): 20,
}

# Friends and constraints
friends = [
    {
        "name": "Andrew",
        "location": "Golden Gate Park",
        "avail_start": to_minutes("11:45"),
        "avail_end": to_minutes("14:30"),
        "min_duration": 75,
    },
    {
        "name": "Sarah",
        "location": "Pacific Heights",
        "avail_start": to_minutes("16:15"),
        "avail_end": to_minutes("18:45"),
        "min_duration": 15,
    },
    {
        "name": "Nancy",
        "location": "Presidio",
        "avail_start": to_minutes("17:30"),
        "avail_end": to_minutes("19:15"),
        "min_duration": 60,
    },
    {
        "name": "Rebecca",
        "location": "Chinatown",
        "avail_start": to_minutes("9:45"),
        "avail_end": to_minutes("21:30"),
        "min_duration": 90,
    },
    {
        "name": "Robert",
        "location": "The Castro",
        "avail_start": to_minutes("8:30"),
        "avail_end": to_minutes("14:15"),
        "min_duration": 30,
    },
]

def schedule_for_order(order):
    itinerary = []
    curr_loc = start_location
    curr_time = start_time
    total_wait = 0
    total_travel = 0

    for person in order:
        key = (curr_loc, person["location"])
        if key not in travel:
            return None  # No travel path
        ttime = travel[key]
        total_travel += ttime
        arrival = curr_time + ttime
        start_meet = max(arrival, person["avail_start"])
        wait = max(0, start_meet - arrival)
        total_wait += wait
        end_meet = start_meet + person["min_duration"]
        if end_meet > person["avail_end"]:
            return None  # Cannot fit within availability

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start": start_meet,
            "end": end_meet,
            "arrival": arrival,  # internal use for waiting computation
        })
        curr_loc = person["location"]
        curr_time = end_meet

    finish_time = curr_time
    return {
        "itinerary": itinerary,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "finish_time": finish_time
    }

# Search over all subsets and permutations to maximize number of friends met
best_plan = None
best_score = None  # tuple for comparison

n = len(friends)
found_at_size = None

for k in range(n, 0, -1):
    feasible_plans = []
    for subset in itertools.combinations(friends, k):
        for order in itertools.permutations(subset):
            plan = schedule_for_order(order)
            if plan is not None:
                feasible_plans.append((order, plan))
    if feasible_plans:
        # Choose optimal among size k:
        # Priority: minimize total_wait, then earliest finish_time, then minimize total_travel, then lexicographic by names
        def score(entry):
            order, plan = entry
            names = tuple(p["name"] for p in order)
            return (plan["total_wait"], plan["finish_time"], plan["total_travel"], names)
        best_entry = min(feasible_plans, key=score)
        best_plan = best_entry
        found_at_size = k
        break  # No need to check smaller subsets

# Build output
output = {"itinerary": []}
if best_plan:
    order, plan = best_plan
    for item in plan["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt(item["start"]),
            "end_time": fmt(item["end"]),
        })

print(json.dumps(output, indent=2))