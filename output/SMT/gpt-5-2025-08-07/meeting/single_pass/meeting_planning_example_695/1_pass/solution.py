# Requires z3-solver (pip install z3-solver)
from z3 import Solver, Int, And, sat
from itertools import combinations, permutations
import json

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def from_minutes(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def build_data():
    # Travel times (directed, in minutes)
    travel = {
        "Bayview": {
            "Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20,
            "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17,
            "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19,
            "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22,
            "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20,
            "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21,
            "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11,
            "The Castro": 16, "Presidio": 11, "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9,
            "The Castro": 21, "Presidio": 14, "Pacific Heights": 7
        }
    }

    start_of_day = to_minutes("09:00")  # Arrival at Bayview

    # Friend availability windows and minimum durations
    friends = {
        "Paul":     {"loc": "Nob Hill",       "win": (to_minutes("16:15"), to_minutes("21:15")), "dur": 60},
        "Carol":    {"loc": "Union Square",   "win": (to_minutes("18:00"), to_minutes("20:15")), "dur": 120},
        "Patricia": {"loc": "Chinatown",      "win": (to_minutes("20:00"), to_minutes("21:30")), "dur": 75},
        "Karen":    {"loc": "The Castro",     "win": (to_minutes("17:00"), to_minutes("19:00")), "dur": 45},
        "Nancy":    {"loc": "Presidio",       "win": (to_minutes("11:45"), to_minutes("22:00")), "dur": 30},
        "Jeffrey":  {"loc": "Pacific Heights","win": (to_minutes("20:00"), to_minutes("20:45")), "dur": 45},
        "Matthew":  {"loc": "Russian Hill",   "win": (to_minutes("15:45"), to_minutes("21:45")), "dur": 75},
    }

    return travel, friends, start_of_day

def feasible_schedule_for_order(order, travel, friends, start_of_day):
    # Z3 variables for start times (integer minutes from 00:00)
    s = {name: Int(f"s_{name}") for name in order}
    z = Solver()

    # Meeting window and duration constraints
    for name in order:
        wstart, wend = friends[name]["win"]
        dur = friends[name]["dur"]
        z.add(s[name] >= wstart)
        z.add(s[name] + dur <= wend)

    # Start at Bayview at 09:00 then travel to first meeting
    first = order[0]
    first_loc = friends[first]["loc"]
    z.add(s[first] >= start_of_day + travel["Bayview"][first_loc])

    # Sequencing and travel time constraints
    for a, b in zip(order[:-1], order[1:]):
        loc_a = friends[a]["loc"]
        loc_b = friends[b]["loc"]
        dur_a = friends[a]["dur"]
        # Next meeting must start after we finish meeting a and travel to b
        z.add(s[b] >= s[a] + dur_a + travel[loc_a][loc_b])

    if z.check() != sat:
        return None

    m = z.model()
    schedule = []
    for name in order:
        st = m[s[name]].as_long()
        et = st + friends[name]["dur"]
        schedule.append({
            "name": name,
            "start": st,
            "end": et,
            "loc": friends[name]["loc"]
        })

    # Ensure chronological order by start time (should already be due to constraints)
    schedule.sort(key=lambda e: e["start"])
    return schedule

def optimize_itinerary(travel, friends, start_of_day):
    names = list(friends.keys())

    best = None
    best_key = None

    # Preference tie-breaker: prefer sets including these friends in order
    # We choose to prefer Patricia, Karen, Paul, Matthew, Nancy, then Carol, then Jeffrey
    pref_order = ["Patricia", "Karen", "Paul", "Matthew", "Nancy", "Carol", "Jeffrey"]

    for k in range(len(names), 0, -1):
        found_for_k = False
        for subset in combinations(names, k):
            subset_set = set(subset)
            # Preference vector: 1 if friend is in subset, else 0, in pref_order order
            pref_vec = tuple(1 if p in subset_set else 0 for p in pref_order)
            for order in permutations(subset):
                sched = feasible_schedule_for_order(order, travel, friends, start_of_day)
                if sched is None:
                    continue
                # Compute finish time of the last meeting
                finish_time = max(e["end"] for e in sched)
                # Key to maximize: (k, pref_vec, -finish_time)
                key = (k, pref_vec, -finish_time)
                if best is None or key > best_key:
                    best = sched
                    best_key = key
                    found_for_k = True
        if found_for_k:
            break

    return best

def main():
    travel, friends, start_of_day = build_data()
    best = optimize_itinerary(travel, friends, start_of_day)

    if not best:
        print(json.dumps({"itinerary": []}))
        return

    # Build output in required JSON format
    itinerary = []
    for e in best:
        itinerary.append({
            "action": "meet",
            "person": e["name"],
            "start_time": from_minutes(e["start"]),
            "end_time": from_minutes(e["end"])
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()