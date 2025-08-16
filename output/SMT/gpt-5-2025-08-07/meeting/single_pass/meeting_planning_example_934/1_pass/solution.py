# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Define travel times (in minutes) between locations
travel = {
    "Nob Hill": {
        "Embarcadero": 9, "The Castro": 17, "Haight-Ashbury": 13, "Union Square": 7,
        "North Beach": 8, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 17,
        "Marina District": 11, "Russian Hill": 5
    },
    "Embarcadero": {
        "Nob Hill": 10, "The Castro": 25, "Haight-Ashbury": 21, "Union Square": 10,
        "North Beach": 5, "Pacific Heights": 11, "Chinatown": 7, "Golden Gate Park": 25,
        "Marina District": 12, "Russian Hill": 8
    },
    "The Castro": {
        "Nob Hill": 16, "Embarcadero": 22, "Haight-Ashbury": 6, "Union Square": 19,
        "North Beach": 20, "Pacific Heights": 16, "Chinatown": 22, "Golden Gate Park": 11,
        "Marina District": 21, "Russian Hill": 18
    },
    "Haight-Ashbury": {
        "Nob Hill": 15, "Embarcadero": 20, "The Castro": 6, "Union Square": 19,
        "North Beach": 19, "Pacific Heights": 12, "Chinatown": 19, "Golden Gate Park": 7,
        "Marina District": 17, "Russian Hill": 17
    },
    "Union Square": {
        "Nob Hill": 9, "Embarcadero": 11, "The Castro": 17, "Haight-Ashbury": 18,
        "North Beach": 10, "Pacific Heights": 15, "Chinatown": 7, "Golden Gate Park": 22,
        "Marina District": 18, "Russian Hill": 13
    },
    "North Beach": {
        "Nob Hill": 7, "Embarcadero": 6, "The Castro": 23, "Haight-Ashbury": 18,
        "Union Square": 7, "Pacific Heights": 8, "Chinatown": 6, "Golden Gate Park": 22,
        "Marina District": 9, "Russian Hill": 4
    },
    "Pacific Heights": {
        "Nob Hill": 8, "Embarcadero": 10, "The Castro": 16, "Haight-Ashbury": 11,
        "Union Square": 12, "North Beach": 9, "Chinatown": 11, "Golden Gate Park": 15,
        "Marina District": 6, "Russian Hill": 7
    },
    "Chinatown": {
        "Nob Hill": 9, "Embarcadero": 5, "The Castro": 22, "Haight-Ashbury": 19,
        "Union Square": 7, "North Beach": 3, "Pacific Heights": 10, "Golden Gate Park": 23,
        "Marina District": 12, "Russian Hill": 7
    },
    "Golden Gate Park": {
        "Nob Hill": 20, "Embarcadero": 25, "The Castro": 13, "Haight-Ashbury": 7,
        "Union Square": 22, "North Beach": 23, "Pacific Heights": 16, "Chinatown": 23,
        "Marina District": 16, "Russian Hill": 19
    },
    "Marina District": {
        "Nob Hill": 12, "Embarcadero": 14, "The Castro": 22, "Haight-Ashbury": 16,
        "Union Square": 16, "North Beach": 11, "Pacific Heights": 7, "Chinatown": 15,
        "Golden Gate Park": 18, "Russian Hill": 8
    },
    "Russian Hill": {
        "Nob Hill": 5, "Embarcadero": 8, "The Castro": 21, "Haight-Ashbury": 17,
        "Union Square": 10, "North Beach": 5, "Pacific Heights": 7, "Chinatown": 9,
        "Golden Gate Park": 21, "Marina District": 7
    }
}

# People, locations, availability windows, and minimum meeting durations (minutes)
persons = {
    "Mary":    {"loc": "Embarcadero",     "start": to_min("20:00"), "end": to_min("21:15"), "min": 75},
    "Kenneth": {"loc": "The Castro",      "start": to_min("11:15"), "end": to_min("19:15"), "min": 30},
    "Joseph":  {"loc": "Haight-Ashbury",  "start": to_min("20:00"), "end": to_min("22:00"), "min": 120},
    "Sarah":   {"loc": "Union Square",    "start": to_min("11:45"), "end": to_min("14:30"), "min": 90},
    "Thomas":  {"loc": "North Beach",     "start": to_min("19:15"), "end": to_min("19:45"), "min": 15},
    "Daniel":  {"loc": "Pacific Heights", "start": to_min("13:45"), "end": to_min("20:30"), "min": 15},
    "Richard": {"loc": "Chinatown",       "start": to_min("08:00"), "end": to_min("18:45"), "min": 30},
    "Mark":    {"loc": "Golden Gate Park","start": to_min("17:30"), "end": to_min("21:30"), "min": 120},
    "David":   {"loc": "Marina District", "start": to_min("20:00"), "end": to_min("21:00"), "min": 60},
    "Karen":   {"loc": "Russian Hill",    "start": to_min("13:15"), "end": to_min("18:30"), "min": 120},
}

home_loc = "Nob Hill"
arrival_time = to_min("09:00")

opt = Optimize()
opt.set(priority='lex')

start_vars = {}
end_vars = {}
meet_vars = {}

# Variables and basic constraints
for p, data in persons.items():
    start_vars[p] = Int(f"start_{p}")
    end_vars[p] = Int(f"end_{p}")
    meet_vars[p] = Bool(f"meet_{p}")

    s_min = data["start"]
    e_max = data["end"]
    d_min = data["min"]
    loc = data["loc"]
    travel_from_home = travel[home_loc][loc]

    # Bounds and meeting constraints when chosen
    opt.add(start_vars[p] >= 0, end_vars[p] >= 0)
    opt.add(Implies(meet_vars[p],
                    And(
                        start_vars[p] >= s_min,
                        end_vars[p] <= e_max,
                        end_vars[p] - start_vars[p] >= d_min,
                        # Must be physically reachable from start of day at Nob Hill
                        start_vars[p] >= arrival_time + travel_from_home
                    )))
    # If not meeting, allow start=end for cleanliness
    opt.add(Implies(Not(meet_vars[p]), end_vars[p] == start_vars[p]))

# Pairwise sequencing with travel times if both meetings occur
people = list(persons.keys())
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        pi = people[i]
        pj = people[j]
        li = persons[pi]["loc"]
        lj = persons[pj]["loc"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        opt.add(Implies(And(meet_vars[pi], meet_vars[pj]),
                        Or(end_vars[pi] + tij <= start_vars[pj],
                           end_vars[pj] + tji <= start_vars[pi])))

# Objectives: maximize number of friends met, then maximize total meeting time
count_meet = Sum([If(meet_vars[p], 1, 0) for p in people])
total_time = Sum([If(meet_vars[p], end_vars[p] - start_vars[p], 0) for p in people])
opt.maximize(count_meet)
opt.maximize(total_time)

if opt.check() == sat:
    model = opt.model()
    itinerary = []
    # Extract chosen meetings
    chosen = []
    for p in people:
        if is_true(model.evaluate(meet_vars[p])):
            s = model.evaluate(start_vars[p]).as_long()
            e = model.evaluate(end_vars[p]).as_long()
            chosen.append((s, {
                "action": "meet",
                "person": p,
                "start_time": to_hhmm(s),
                "end_time": to_hhmm(e)
            }))
    chosen.sort(key=lambda x: x[0])
    itinerary = [entry for _, entry in chosen]
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    # No feasible schedule
    print(json.dumps({"itinerary": []}, indent=2))