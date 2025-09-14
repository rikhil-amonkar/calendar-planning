# SOLUTION:
import json
from z3 import *

def parse_time(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input data
start_location = "Bayview"
start_time = parse_time("9:00")

# Travel times (minutes)
travel = {
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Union Square"): 17,

    ("North Beach", "Bayview"): 22,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,

    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Union Square"): 22,

    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 17,

    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Haight-Ashbury"): 18,
}

# People and their constraints
people = [
    {
        "name": "Barbara",
        "location": "North Beach",
        "avail_start": parse_time("13:45"),
        "avail_end": parse_time("20:15"),
        "min_dur": 60
    },
    {
        "name": "Margaret",
        "location": "Presidio",
        "avail_start": parse_time("10:15"),
        "avail_end": parse_time("15:15"),
        "min_dur": 30
    },
    {
        "name": "Kevin",
        "location": "Haight-Ashbury",
        "avail_start": parse_time("20:00"),
        "avail_end": parse_time("20:45"),
        "min_dur": 30
    },
    {
        "name": "Kimberly",
        "location": "Union Square",
        "avail_start": parse_time("7:45"),
        "avail_end": parse_time("16:45"),
        "min_dur": 30
    },
]

n = len(people)

# Z3 model
opt = Optimize()
opt.set(priority='lex')

# Variables
sel = {}
first = {}
start = {}
end = {}
dur = {}
before = {}

for i, p in enumerate(people):
    sel[i] = Bool(f"sel_{i}_{p['name']}")
    first[i] = Bool(f"first_{i}_{p['name']}")
    start[i] = Int(f"start_{i}_{p['name']}")
    end[i] = Int(f"end_{i}_{p['name']}")
    dur[i] = Int(f"dur_{i}_{p['name']}")
    for j, q in enumerate(people):
        if i != j:
            before[(i, j)] = Bool(f"before_{i}_{j}")

# Basic bounds and meeting constraints
for i, p in enumerate(people):
    # If selected: adhere to availability, duration, and end = start + dur
    opt.add(Implies(sel[i], And(
        start[i] >= p["avail_start"],
        end[i] <= p["avail_end"],
        end[i] == start[i] + dur[i],
        dur[i] >= p["min_dur"],
        dur[i] <= p["avail_end"] - p["avail_start"]
    )))
    # If not selected: pin times to 0 and not first
    opt.add(Implies(Not(sel[i]), And(
        start[i] == 0,
        end[i] == 0,
        dur[i] == 0,
        Not(first[i])
    )))
    # Non-negativity (redundant when not selected but safe)
    opt.add(start[i] >= 0, end[i] >= 0, dur[i] >= 0)

# Precedence constraints and non-overlap when both are selected
for i in range(n):
    for j in range(i+1, n):
        li = people[i]["location"]
        lj = people[j]["location"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        # If i before j then timing with travel
        opt.add(Implies(before[(i, j)], And(sel[i], sel[j], end[i] + tij <= start[j])))
        opt.add(Implies(before[(j, i)], And(sel[i], sel[j], end[j] + tji <= start[i])))
        # If both selected, one must be before the other
        opt.add(Implies(And(sel[i], sel[j]), Or(before[(i, j)], before[(j, i)])))
        # Can't be both ways
        opt.add(Not(And(before[(i, j)], before[(j, i)])))

# First meeting constraints
for i, p in enumerate(people):
    # Being first implies selected
    opt.add(Implies(first[i], sel[i]))
    # No one precedes the first
    for j in range(n):
        if i != j:
            opt.add(Implies(first[i], Not(before[(j, i)])))
    # Earliest feasible arrival from starting point to the first meeting
    opt.add(Implies(first[i], start[i] >= start_time + travel[(start_location, p["location"])]))
    # Every selected meeting is either first or has some predecessor
    predecessors = [before[(j, i)] for j in range(n) if j != i]
    if predecessors:
        opt.add(Implies(sel[i], Or(first[i], Or(predecessors))))
    else:
        opt.add(Implies(sel[i], first[i]))

# Exactly one first if at least one meeting is selected
total_sel = Sum([If(sel[i], 1, 0) for i in range(n)])
total_first = Sum([If(first[i], 1, 0) for i in range(n)])
opt.add(total_first == If(total_sel == 0, 0, 1))

# Objectives:
# 1) Maximize number of meetings
opt.maximize(total_sel)

# 2) Minimize end time of the last meeting (tie-breaker)
last_end = Int("last_end")
opt.add(last_end >= 0)
for i in range(n):
    opt.add(last_end >= end[i])
opt.minimize(last_end)

# Solve
if opt.check() != sat:
    output = {"itinerary": []}
    print(json.dumps(output))
else:
    m = opt.model()
    chosen = []
    for i, p in enumerate(people):
        if is_true(m.eval(sel[i])):
            s_min = m.eval(start[i]).as_long()
            e_min = m.eval(end[i]).as_long()
            chosen.append({
                "person": p["name"],
                "location": p["location"],
                "start_min": s_min,
                "end_min": e_min
            })
    # Sort by start time
    chosen.sort(key=lambda x: x["start_min"])
    itinerary = []
    for item in chosen:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": to_hhmm(item["start_min"]),
            "end_time": to_hhmm(item["end_min"])
        })
    print(json.dumps({"itinerary": itinerary}))