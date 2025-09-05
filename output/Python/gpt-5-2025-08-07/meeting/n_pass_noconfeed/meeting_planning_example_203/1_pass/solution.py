"""SOLUTION:
Compute optimal meeting schedule in San Francisco given constraints.
The script explores schedules algorithmically and outputs a JSON itinerary.
"""

import itertools
import json

# Time utilities
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
start_location = "Financial District"
start_time = to_minutes(9, 0)  # 9:00

# Directed travel times in minutes
travel = {
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Mission District", "Financial District"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Pacific Heights"): 16,
}

# People constraints
people = [
    {
        "name": "David",
        "location": "Fisherman's Wharf",
        "window_start": to_minutes(10, 45),
        "window_end": to_minutes(15, 30),
        "min_duration": 15,
    },
    {
        "name": "Timothy",
        "location": "Pacific Heights",
        "window_start": to_minutes(9, 0),
        "window_end": to_minutes(15, 30),
        "min_duration": 75,
    },
    {
        "name": "Robert",
        "location": "Mission District",
        "window_start": to_minutes(12, 15),
        "window_end": to_minutes(19, 45),
        "min_duration": 90,
    },
]

# Helper to fetch travel time
def get_travel(a, b):
    if a == b:
        return 0
    return travel[(a, b)]

# Feasibility check for remainder with minimal durations
def remainder_feasible(curr_time, curr_loc, remaining_order):
    time = curr_time
    loc = curr_loc
    for p in remaining_order:
        time += get_travel(loc, p["location"])
        if time < p["window_start"]:
            time = p["window_start"]
        # must fit min duration
        if time + p["min_duration"] > p["window_end"]:
            return False
        time += p["min_duration"]
        loc = p["location"]
    return True

# Build detailed schedule for a given order using greedy-max end times while ensuring feasibility
def build_schedule(order):
    itinerary = []
    total_meeting = 0
    total_travel = 0

    curr_time = start_time
    curr_loc = start_location

    for idx, p in enumerate(order):
        # travel to next person's location
        t_travel = get_travel(curr_loc, p["location"])
        total_travel += t_travel
        arrival = curr_time + t_travel
        start_meet = max(arrival, p["window_start"])

        # must be able to fit min duration
        if start_meet + p["min_duration"] > p["window_end"]:
            return None  # infeasible

        # Choose latest possible end time that still allows remainder to be feasible with minimal durations
        lo = start_meet + p["min_duration"]
        hi = p["window_end"]
        best_end = None

        # Binary search over minute granularity for max feasible end
        remaining = order[idx + 1 :]
        low = lo
        high = hi
        while low <= high:
            mid = (low + high) // 2  # candidate end time
            if remainder_feasible(mid, p["location"], remaining):
                best_end = mid
                low = mid + 1
            else:
                high = mid - 1

        if best_end is None:
            return None  # infeasible, though should not happen since at least min duration should pass remainder check at lo

        itinerary.append(
            {
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": fmt_time(start_meet),
                "end_time": fmt_time(best_end),
                "_start_min": start_meet,
                "_end_min": best_end,
            }
        )
        total_meeting += best_end - start_meet
        curr_time = best_end
        curr_loc = p["location"]

    # After all meetings, try to extend the last meeting to the end of their availability if there is slack
    # There is no constraint after the last person, so we can maximize the last meeting to their window end.
    if itinerary:
        last = itinerary[-1]
        # Compute feasible max end = window_end of last person
        last_person = order[-1]
        current_end = last["_end_min"]
        max_end = last_person["window_end"]
        if current_end < max_end:
            # No remainder to restrict, so we can extend to window end
            total_meeting += (max_end - current_end)
            last["_end_min"] = max_end
            last["end_time"] = fmt_time(max_end)

    # Clean itinerary from helper fields
    for entry in itinerary:
        if "_start_min" in entry:
            del entry["_start_min"]
        if "_end_min" in entry:
            del entry["_end_min"]

    return {
        "itinerary": itinerary,
        "total_meeting": total_meeting,
        "total_travel": total_travel,
        "end_time": curr_time if not itinerary else to_minutes(int(itinerary[-1]["end_time"].split(":")[0]), int(itinerary[-1]["end_time"].split(":")[1])),
        "met_count": len(itinerary),
    }

# Explore all subsets and permutations to find the optimal schedule
best_plan = None
best_key = None

# Generate all non-empty subsets
for r in range(1, len(people) + 1):
    for subset in itertools.permutations(people, r):
        plan = build_schedule(list(subset))
        if plan is None:
            continue
        # Objective: maximize met_count, then total_meeting
        # Tie-breakers: minimize total_travel, then earliest end_time, then lexicographic order of people names
        key = (
            plan["met_count"],
            plan["total_meeting"],
            -plan["total_travel"],
            -plan["end_time"],  # negative because we want earliest end (min), but tuple chooses max
            tuple(p["name"] for p in subset),
        )
        if best_key is None or key > best_key:
            best_key = key
            best_plan = plan

# Ensure a result exists
if best_plan is None:
    output = {"itinerary": []}
else:
    output = {"itinerary": best_plan["itinerary"]}

print(json.dumps(output, ensure_ascii=False))