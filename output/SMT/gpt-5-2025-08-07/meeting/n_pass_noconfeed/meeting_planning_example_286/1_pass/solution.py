# Requires: python -m pip install z3-solver
from z3 import Optimize, Int, sat
import itertools
import json

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Base data
start_location = "Union Square"
start_time = 9 * 60  # 9:00 in minutes since midnight

# Travel times in minutes (asymmetric allowed)
travel = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Sunset District"): 26,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Sunset District"): 23,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Bayview"): 22,
}

people = {
    "Rebecca": {
        "location": "Mission District",
        "start": 11 * 60 + 30,   # 11:30
        "end": 20 * 60 + 15,     # 20:15
        "min_dur": 120
    },
    "Karen": {
        "location": "Bayview",
        "start": 12 * 60 + 45,   # 12:45
        "end": 15 * 60 + 0,      # 15:00
        "min_dur": 120
    },
    "Carol": {
        "location": "Sunset District",
        "start": 10 * 60 + 15,   # 10:15
        "end": 11 * 60 + 45,     # 11:45
        "min_dur": 30
    }
}

def solve_order(order):
    """
    Given an ordered tuple of people, attempt to find start times that satisfy:
    - travel times from start location and between meetings
    - availability windows
    - minimum durations
    Returns (is_feasible, itinerary_list, last_end_time) for this order.
    """
    if not order:
        return True, [], start_time

    opt = Optimize()

    n = len(order)
    s_vars = [Int(f"s_{i}") for i in range(n)]  # start times (minutes since midnight)

    # Fixed minimum durations
    durs = [people[p]["min_dur"] for p in order]

    # Constraints per meeting
    # First meeting arrival from starting point
    first_loc = people[order[0]]["location"]
    if (start_location, first_loc) not in travel:
        return False, None, None
    arr0 = start_time + travel[(start_location, first_loc)]
    opt.add(s_vars[0] >= arr0)
    opt.add(s_vars[0] >= people[order[0]]["start"])
    opt.add(s_vars[0] + durs[0] <= people[order[0]]["end"])

    # Subsequent meetings
    for i in range(1, n):
        prev_loc = people[order[i-1]]["location"]
        curr_loc = people[order[i]]["location"]
        if (prev_loc, curr_loc) not in travel:
            return False, None, None
        # arrival time after finishing previous + travel
        prev_end = s_vars[i-1] + durs[i-1]
        arr_i = prev_end + travel[(prev_loc, curr_loc)]
        opt.add(s_vars[i] >= arr_i)
        opt.add(s_vars[i] >= people[order[i]]["start"])
        opt.add(s_vars[i] + durs[i] <= people[order[i]]["end"])

    # Minimize the finish time of the last meeting for this order
    last_end = s_vars[-1] + durs[-1]
    opt.minimize(last_end)

    if opt.check() != sat:
        return False, None, None

    model = opt.model()
    itinerary = []
    for i, person in enumerate(order):
        start_m = model[s_vars[i]].as_long()
        end_m = start_m + durs[i]
        itinerary.append({
            "action": "meet",
            "location": people[person]["location"],
            "person": person,
            "start_time": minutes_to_str(start_m),
            "end_time": minutes_to_str(end_m)
        })

    last_end_val = model.eval(last_end).as_long()
    return True, itinerary, last_end_val

def compute_best_schedule():
    names = list(people.keys())
    best = None

    # Try to maximize number of meetings; break ties by earliest finish
    for k in range(len(names), 0, -1):
        best_for_k = None
        for order in itertools.permutations(names, k):
            feasible, itinerary, finish_time = solve_order(order)
            if feasible:
                if (best_for_k is None) or (finish_time < best_for_k[2]):
                    best_for_k = (order, itinerary, finish_time)
        if best_for_k:
            best = best_for_k
            break

    if best:
        return {"itinerary": best[1]}
    else:
        return {"itinerary": []}

if __name__ == "__main__":
    result = compute_best_schedule()
    print(json.dumps(result, ensure_ascii=False))