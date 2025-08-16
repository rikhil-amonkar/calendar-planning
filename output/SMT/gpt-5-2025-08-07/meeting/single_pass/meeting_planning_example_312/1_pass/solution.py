# Requires: pip install z3-solver
from z3 import Int, Optimize, Sum, sat
import itertools
import json

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Data
origin_loc = "Richmond District"
origin_time = to_minutes("09:00")

people = [
    {
        "name": "Sarah",
        "loc": "Sunset District",
        "avail_start": to_minutes("10:45"),
        "avail_end": to_minutes("19:00"),
        "min_duration": 30,
    },
    {
        "name": "Richard",
        "loc": "Haight-Ashbury",
        "avail_start": to_minutes("11:45"),
        "avail_end": to_minutes("15:45"),
        "min_duration": 90,
    },
    {
        "name": "Elizabeth",
        "loc": "Mission District",
        "avail_start": to_minutes("11:00"),
        "avail_end": to_minutes("17:15"),
        "min_duration": 120,
    },
    {
        "name": "Michelle",
        "loc": "Golden Gate Park",
        "avail_start": to_minutes("18:15"),
        "avail_end": to_minutes("20:45"),
        "min_duration": 90,
    },
]

# Directed travel times (in minutes)
T = {
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

def solve_order(order):
    n = len(order)
    if n == 0:
        return None

    opt = Optimize()

    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    wait_vars = [Int(f"wait_{i}") for i in range(n)]

    # Constraints for each meeting
    for i, p in enumerate(order):
        # Basic domain
        opt.add(start_vars[i] >= 0)
        opt.add(end_vars[i] == start_vars[i] + p["min_duration"])
        # Availability window
        opt.add(start_vars[i] >= p["avail_start"])
        opt.add(end_vars[i] <= p["avail_end"])

    # Travel and waiting constraints
    # First meeting from origin
    first_loc = order[0]["loc"]
    origin_arrival_lb = origin_time + T[origin_loc][first_loc]
    opt.add(start_vars[0] >= origin_arrival_lb)
    opt.add(wait_vars[0] == start_vars[0] - origin_arrival_lb)
    opt.add(wait_vars[0] >= 0)

    # Subsequent meetings follow chain with travel
    for i in range(1, n):
        prev_loc = order[i - 1]["loc"]
        curr_loc = order[i]["loc"]
        travel = T[prev_loc][curr_loc]
        # next start must be no earlier than prev end + travel
        opt.add(start_vars[i] >= end_vars[i - 1] + travel)
        # waiting is the slack beyond prev end + travel
        opt.add(wait_vars[i] == start_vars[i] - (end_vars[i - 1] + travel))
        opt.add(wait_vars[i] >= 0)

    # Objectives: minimize end time of last meeting, then minimize total waiting
    total_wait = Sum(wait_vars)
    opt.minimize(end_vars[-1])
    opt.minimize(total_wait)

    if opt.check() != sat:
        return None

    model = opt.model()
    starts = [model[s].as_long() for s in start_vars]
    ends = [model[e].as_long() for e in end_vars]
    waits = [model[w].as_long() for w in wait_vars]

    itinerary = []
    for i, p in enumerate(order):
        itinerary.append({
            "action": "meet",
            "person": p["name"],
            "start_time": to_hhmm(starts[i]),
            "end_time": to_hhmm(ends[i]),
        })

    # Compute total travel for tie-breaking
    total_travel = T[origin_loc][order[0]["loc"]] + sum(
        T[order[i - 1]["loc"]][order[i]["loc"]] for i in range(1, n)
    )

    result = {
        "itinerary": itinerary,
        "last_end": ends[-1],
        "total_wait": sum(waits),
        "total_travel": total_travel,
    }
    return result

def pick_best_schedule():
    best = None
    # Maximize number of people first
    for r in range(len(people), 0, -1):
        any_found = False
        for subset in itertools.combinations(people, r):
            for order in itertools.permutations(subset):
                sol = solve_order(order)
                if sol is None:
                    continue
                any_found = True
                if best is None:
                    best = (r, sol)
                else:
                    best_count, best_sol = best
                    # Tie-breakers: earliest last_end, then minimal total_wait, then minimal total_travel
                    key = (r, -sol["last_end"], -sol["total_wait"], -sol["total_travel"])
                    best_key = (best_count, -best_sol["last_end"], -best_sol["total_wait"], -best_sol["total_travel"])
                    if key > best_key:
                        best = (r, sol)
        if any_found:
            break
    return best[1] if best else None

def main():
    best = pick_best_schedule()
    if best is None:
        print(json.dumps({"itinerary": []}))
    else:
        # Only output the itinerary as specified
        print(json.dumps({"itinerary": best["itinerary"]}))

if __name__ == "__main__":
    main()