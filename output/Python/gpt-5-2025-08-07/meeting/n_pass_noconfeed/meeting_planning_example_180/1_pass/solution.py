import json
from itertools import permutations, chain, combinations

# Input variables based on the given problem
start_location = "North Beach"
start_time_str = "9:00"

# Travel times (in minutes), directional
travel_times = {
    ("North Beach", "Mission District"): 18,
    ("North Beach", "The Castro"): 22,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "The Castro"): 7,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Mission District"): 7,
}
# Add zero travel for same-location moves
for loc in {"North Beach", "Mission District", "The Castro"}:
    travel_times[(loc, loc)] = 0

# Friends with availability and minimum meeting durations
friends = [
    {
        "name": "James",
        "location": "Mission District",
        "available_start": "12:45",
        "available_end": "14:00",
        "min_duration": 75,
    },
    {
        "name": "Robert",
        "location": "The Castro",
        "available_start": "12:45",
        "available_end": "15:15",
        "min_duration": 30,
    },
]

# Utility functions
def parse_time(tstr):
    # tstr like '9:00', '13:30'
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s) + 1))

# Preprocess friend data
for f in friends:
    f["available_start_min"] = parse_time(f["available_start"])
    f["available_end_min"] = parse_time(f["available_end"])

start_time_min = parse_time(start_time_str)

def get_travel(a, b):
    return travel_times.get((a, b), None)

def plan_for_order(order, start_loc, start_time):
    # Recursive search over possible minute-by-minute end times to maximize total meeting duration
    best_result = None  # tuple: (total_people_met, total_meeting_minutes, -total_wait_minutes, itinerary_list)

    def recurse(idx, current_loc, current_time, itinerary, total_meeting, total_wait):
        nonlocal best_result

        if idx == len(order):
            score = (len(itinerary), total_meeting, -total_wait, itinerary)
            if best_result is None or score > best_result:
                best_result = score
            return

        person = order[idx]
        t_travel = get_travel(current_loc, person["location"])
        if t_travel is None:
            return  # unreachable due to missing travel time
        arrival = current_time + t_travel
        start_meet = max(arrival, person["available_start_min"])
        # waiting time if arrive early
        waiting = max(0, person["available_start_min"] - arrival)

        min_end = start_meet + person["min_duration"]
        max_end = person["available_end_min"]

        if min_end > max_end:
            # infeasible to meet this person given current timeline
            return

        # Try all feasible end times (minute precision)
        for end_meet in range(min_end, max_end + 1):
            new_itinerary_entry = {
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": fmt_time(start_meet),
                "end_time": fmt_time(end_meet),
            }
            recurse(
                idx + 1,
                person["location"],
                end_meet,
                itinerary + [new_itinerary_entry],
                total_meeting + (end_meet - start_meet),
                total_wait + waiting,
            )

    recurse(0, start_loc, start_time, [], 0, 0)
    return best_result  # could be None if infeasible

# Explore all subsets and permutations, choose the best by:
# 1) Maximize number of people met
# 2) Maximize total meeting minutes
# 3) Minimize total waiting minutes
overall_best = None

# We only consider non-empty subsets (meeting nobody is trivial and not optimal)
for subset in powerset(friends):
    if not subset:
        continue
    for order in permutations(subset):
        result = plan_for_order(order, start_location, start_time_min)
        if result is None:
            continue
        # result is (people_met, total_meeting_minutes, -total_wait_minutes, itinerary)
        if overall_best is None or result > overall_best:
            overall_best = result

# If for some reason nothing feasible, output empty itinerary
final_itinerary = []
if overall_best is not None:
    final_itinerary = overall_best[3]

output = {
    "itinerary": final_itinerary
}

print(json.dumps(output, ensure_ascii=False))