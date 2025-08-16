# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, sat
import json

def to_min(hhmm):
    h, m = hhmm.split(":")
    return int(h) * 60 + int(m)

def min_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def solve():
    # Travel times (minutes) as given
    places = [
        "Sunset District",
        "Russian Hill",
        "The Castro",
        "Richmond District",
        "Marina District",
        "North Beach",
        "Union Square",
        "Golden Gate Park",
    ]

    travel_pairs = {
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 29,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Golden Gate Park"): 11,

        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11,
        ("Russian Hill", "Golden Gate Park"): 21,

        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Golden Gate Park"): 11,

        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Golden Gate Park"): 9,

        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Golden Gate Park"): 18,

        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Golden Gate Park"): 22,

        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Golden Gate Park"): 22,

        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Union Square"): 22,
    }

    # Build travel dict of dicts for easy access
    travel = {p: {} for p in places}
    for (a, b), t in travel_pairs.items():
        travel[a][b] = t

    # Friends data
    # Times in minutes from 00:00
    friends = {
        "Karen":     {"loc": "Russian Hill",     "start": 20*60+45, "end": 21*60+45, "dur": 60},
        "Jessica":   {"loc": "The Castro",       "start": 15*60+45, "end": 19*60+30, "dur": 60},
        "Matthew":   {"loc": "Richmond District","start": 7*60+30,  "end": 15*60+15, "dur": 15},
        "Michelle":  {"loc": "Marina District",  "start": 10*60+30, "end": 18*60+45, "dur": 75},
        "Carol":     {"loc": "North Beach",      "start": 12*60,    "end": 17*60,    "dur": 90},
        "Stephanie": {"loc": "Union Square",     "start": 10*60+45, "end": 14*60+15, "dur": 30},
        "Linda":     {"loc": "Golden Gate Park", "start": 10*60+45, "end": 22*60,    "dur": 90},
    }

    start_place = "Sunset District"
    arrive_time = 9*60  # 09:00

    people = list(friends.keys())
    n = len(people)

    # Z3 variables
    opt = Optimize()
    s_vars = {p: Int(f"s_{p}") for p in people}      # start times
    meet_vars = {p: Bool(f"meet_{p}") for p in people}

    # Pairwise ordering booleans
    before = {}
    for i in range(n):
        for j in range(n):
            if i == j: 
                continue
            before[(people[i], people[j])] = Bool(f"before_{people[i]}_{people[j]}")

    # Constraints
    for p in people:
        loc = friends[p]["loc"]
        a_start = friends[p]["start"]
        a_end = friends[p]["end"]
        dur = friends[p]["dur"]

        # Domain for times
        opt.add(Implies(meet_vars[p], And(s_vars[p] >= 0, s_vars[p] <= 24*60)))
        # Availability window
        opt.add(Implies(meet_vars[p], And(s_vars[p] >= a_start, s_vars[p] + dur <= a_end)))
        # Arrival from starting location
        opt.add(Implies(meet_vars[p], s_vars[p] >= arrive_time + travel[start_place][loc]))

    # Disjunctive no-overlap and travel time between meetings
    for i in range(n):
        for j in range(i+1, n):
            pi = people[i]
            pj = people[j]
            li = friends[pi]["loc"]
            lj = friends[pj]["loc"]
            di = friends[pi]["dur"]
            dj = friends[pj]["dur"]

            bij = before[(pi, pj)]
            bji = before[(pj, pi)]

            # If pi before pj then respect travel and duration
            opt.add(Implies(bij, s_vars[pj] >= s_vars[pi] + di + travel[li][lj]))
            # If pj before pi
            opt.add(Implies(bji, s_vars[pi] >= s_vars[pj] + dj + travel[lj][li]))

            # Can't be both ways
            opt.add(Not(And(bij, bji)))

            # If both are met, one must be before the other
            opt.add(Implies(And(meet_vars[pi], meet_vars[pj]), Or(bij, bji)))
            # If any is not met, we don't constrain ordering between them (can set both false)
            # Optional: avoid spurious True when someone not met
            opt.add(Implies(Not(And(meet_vars[pi], meet_vars[pj])), And(Not(bij), Not(bji))))

    # Objective: maximize number of friends met
    total_met = sum(If(meet_vars[p], 1, 0) for p in people)
    opt.maximize(total_met)

    # Optional tie-breakers to encourage later scheduling (reduces idle before Karen)
    # Minimize waiting before Karen by maximizing earliest start times; mildly guide:
    # Not necessary for feasibility, so we keep solution purely maximizing count.

    if opt.check() != sat:
        # Fallback empty itinerary (shouldn't happen for this instance)
        return {"itinerary": []}

    model = opt.model()

    meetings = []
    for p in people:
        if model.eval(meet_vars[p], model_completion=True):
            s = model.eval(s_vars[p]).as_long()
            e = s + friends[p]["dur"]
            meetings.append((p, s, e))

    # Sort by start time
    meetings.sort(key=lambda x: x[1])

    itinerary = []
    for p, s, e in meetings:
        entry = {
            "action": "meet",
            "person": p,
            "start_time": min_to_str(s),
            "end_time": min_to_str(e),
        }
        itinerary.append(entry)

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve()
    # Print JSON dictionary with 'itinerary' as required
    print(json.dumps(result))