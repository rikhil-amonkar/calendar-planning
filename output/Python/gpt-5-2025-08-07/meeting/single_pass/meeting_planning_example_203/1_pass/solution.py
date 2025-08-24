"""SOLUTION:"""
import json
import itertools

# Helper functions for time handling
def parse_time(s):
    h, m = map(int, s.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables: travel times (in minutes)
travel = {
    "Financial District": {
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "Mission District": 17,
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Pacific Heights": 12,
        "Mission District": 22,
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Fisherman's Wharf": 13,
        "Mission District": 15,
    },
    "Mission District": {
        "Financial District": 17,
        "Fisherman's Wharf": 22,
        "Pacific Heights": 16,
    },
}

# Starting point and time
start_location = "Financial District"
start_time = parse_time("9:00")

# Friends with constraints
friends = [
    {
        "name": "David",
        "location": "Fisherman's Wharf",
        "avail_start": parse_time("10:45"),
        "avail_end": parse_time("15:30"),
        "min_duration": 15,
    },
    {
        "name": "Timothy",
        "location": "Pacific Heights",
        "avail_start": parse_time("9:00"),
        "avail_end": parse_time("15:30"),
        "min_duration": 75,
    },
    {
        "name": "Robert",
        "location": "Mission District",
        "avail_start": parse_time("12:15"),
        "avail_end": parse_time("19:45"),
        "min_duration": 90,
    },
]

def schedule_for_order(order):
    n = len(order)
    if n == 0:
        return {
            "feasible": True,
            "starts": [],
            "ends": [],
            "waiting": 0,
            "travel_total": 0,
            "finish_time": start_time,
        }

    earliest_arrivals = [0] * n
    earliest_starts = [0] * n
    earliest_ends = [0] * n

    # Forward pass: as-soon-as-possible schedule
    prev_loc = start_location
    prev_end = start_time
    total_travel = 0
    for i, f in enumerate(order):
        t = travel[prev_loc][f["location"]]
        total_travel += t
        arrival = prev_end + t
        start_i = max(arrival, f["avail_start"])
        end_i = start_i + f["min_duration"]
        if end_i > f["avail_end"]:
            return {"feasible": False}
        earliest_arrivals[i] = arrival
        earliest_starts[i] = start_i
        earliest_ends[i] = end_i
        prev_loc = f["location"]
        prev_end = end_i

    # Backward pass: push meetings later where possible to reduce waiting before next
    back_starts = earliest_starts[:]
    back_ends = earliest_ends[:]
    for i in range(n - 2, -1, -1):
        curr = order[i]
        nxt = order[i + 1]
        t = travel[curr["location"]][nxt["location"]]
        # Latest possible end to arrive by next start
        latest_end_i = min(curr["avail_end"], back_starts[i + 1] - t)
        end_i = min(latest_end_i, curr["avail_end"])
        # Ensure not earlier than earliest feasible end
        end_i = max(end_i, earliest_ends[i])
        # Compute start respecting availability and earliest arrival from previous
        lower_bound_start = max(earliest_arrivals[i], curr["avail_start"])
        start_i_candidate = end_i - curr["min_duration"]
        start_i = max(start_i_candidate, lower_bound_start)
        end_i = start_i + curr["min_duration"]
        back_starts[i] = start_i
        back_ends[i] = end_i

    # Compute waiting between meetings (excluding initial wait since we can depart later)
    waiting = 0
    prev_loc = start_location
    prev_end = start_time
    for i, f in enumerate(order):
        t = travel[prev_loc][f["location"]]
        arrival = prev_end + t
        if i > 0:
            waiting += max(0, back_starts[i] - arrival)
        prev_loc = f["location"]
        prev_end = back_ends[i]

    finish_time = back_ends[-1]
    return {
        "feasible": True,
        "starts": back_starts,
        "ends": back_ends,
        "waiting": waiting,
        "travel_total": total_travel,
        "finish_time": finish_time,
    }

# Evaluate all subsets and permutations to maximize number of meetings and optimize tie-breakers
best = None  # (score_tuple, order, schedule_info)
# Primary: maximize number of meetings (=> minimize negative count)
# Secondary: minimize waiting
# Tertiary: minimize total travel
# Quaternary: minimize finish time
for k in range(len(friends), 0, -1):
    found_in_size = False
    for subset in itertools.combinations(friends, k):
        for order in itertools.permutations(subset):
            res = schedule_for_order(order)
            if not res["feasible"]:
                continue
            score = (-k, res["waiting"], res["travel_total"], res["finish_time"])
            if best is None or score < best[0]:
                best = (score, order, res)
                found_in_size = True
    if found_in_size:
        break

# Build itinerary JSON
itinerary = []
if best is not None:
    order = best[1]
    res = best[2]
    for f, s, e in zip(order, res["starts"], res["ends"]):
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": fmt_time(s),
            "end_time": fmt_time(e),
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))