import json
from itertools import permutations

def time_to_minutes(t):
    # t like '9:00', '13:30'
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (in minutes), directional as provided
travel = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Sunset District": 10,
        "Marina District": 16,
        "Financial District": 26,
        "Union Square": 22
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Sunset District": 15,
        "Marina District": 17,
        "Financial District": 21,
        "Union Square": 17
    },
    "Sunset District": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 15,
        "Marina District": 21,
        "Financial District": 30,
        "Union Square": 30
    },
    "Marina District": {
        "Golden Gate Park": 18,
        "Haight-Ashbury": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Union Square": 16
    },
    "Financial District": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Sunset District": 31,
        "Marina District": 15,
        "Union Square": 9
    },
    "Union Square": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Sunset District": 26,
        "Marina District": 18,
        "Financial District": 9
    }
}

# Start parameters
start_location = "Golden Gate Park"
start_time = time_to_minutes("9:00")

# Friends and constraints
friends = [
    {
        "person": "Sarah",
        "location": "Haight-Ashbury",
        "window_start": time_to_minutes("17:00"),
        "window_end": time_to_minutes("21:30"),
        "min_duration": 105
    },
    {
        "person": "Patricia",
        "location": "Sunset District",
        "window_start": time_to_minutes("17:00"),
        "window_end": time_to_minutes("19:45"),
        "min_duration": 45
    },
    {
        "person": "Matthew",
        "location": "Marina District",
        "window_start": time_to_minutes("9:15"),
        "window_end": time_to_minutes("12:00"),
        "min_duration": 15
    },
    {
        "person": "Joseph",
        "location": "Financial District",
        "window_start": time_to_minutes("14:15"),
        "window_end": time_to_minutes("18:45"),
        "min_duration": 30
    },
    {
        "person": "Robert",
        "location": "Union Square",
        "window_start": time_to_minutes("10:15"),
        "window_end": time_to_minutes("21:45"),
        "min_duration": 15
    }
]

# Helper to get travel time
def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Evaluate a given order: greedily schedule each meeting at earliest feasible time
def evaluate_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0

    for f in order:
        t_travel = get_travel(current_loc, f["location"])
        arrive = current_time + t_travel
        start = max(arrive, f["window_start"])
        end = start + f["min_duration"]
        if end <= f["window_end"]:
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["person"],
                "start_time_min": start,
                "end_time_min": end,
                "travel_in_min": t_travel
            })
            current_loc = f["location"]
            current_time = end
            total_travel += t_travel
        # if infeasible, skip this friend in this order
    last_end = itinerary[-1]["end_time_min"] if itinerary else start_time
    return itinerary, last_end, total_travel

# Explore all subsets and orders by evaluating all permutations
best_itinerary = []
best_last_end = None
best_total_travel = None

# Since we want to maximize number of friends met, try all permutations and pick the
# schedule with maximum meetings; tie-breaker: earliest finish time, then least travel
for r in range(len(friends), 0, -1):
    found_for_this_r = False
    for order in permutations(friends, r):
        itinerary, last_end, total_travel = evaluate_order(order)
        # ensure length equals r (i.e., all in this permutation feasible) OR accept partial within this order?
        # We want the maximum count; evaluate_order may skip infeasible within the order.
        # So just compare lengths.
        if len(itinerary) == 0:
            continue
        if (len(itinerary) > len(best_itinerary) or
            (len(itinerary) == len(best_itinerary) and (best_last_end is None or last_end < best_last_end)) or
            (len(itinerary) == len(best_itinerary) and last_end == best_last_end and (best_total_travel is None or total_travel < best_total_travel))):
            best_itinerary = itinerary
            best_last_end = last_end
            best_total_travel = total_travel
            found_for_this_r = True
    # Early stop if we found a full schedule of size r greater than any smaller r
    # But because evaluate_order might produce fewer than r due to skips, we cannot early stop by r alone.
    # We'll continue scanning all permutations.

# Format output
output = {
    "itinerary": []
}

for item in best_itinerary:
    output["itinerary"].append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": minutes_to_time(item["start_time_min"]),
        "end_time": minutes_to_time(item["end_time_min"])
    })

print(json.dumps(output, indent=2))