# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, is_true
import json

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def mm_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Travel times (minutes), directional
travel = {
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 29,

    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,

    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,

    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
}

# Problem data
start_location = "Sunset District"
arrival_time = to_min("09:00")

people = {
    "Anthony": {
        "location": "Chinatown",
        "window_start": to_min("13:15"),
        "window_end": to_min("14:30"),
        "min_duration": 60,
    },
    "Rebecca": {
        "location": "Russian Hill",
        "window_start": to_min("19:30"),
        "window_end": to_min("21:15"),
        "min_duration": 105,
    },
    "Melissa": {
        "location": "North Beach",
        "window_start": to_min("08:15"),
        "window_end": to_min("13:30"),
        "min_duration": 105,
    },
}

# Z3 model
opt = Optimize()

start = {}
end = {}
meet = {}

for person in people:
    start[person] = Int(f"start_{person}")
    end[person] = Int(f"end_{person}")
    meet[person] = Bool(f"meet_{person}")

    # bounds
    opt.add(start[person] >= 0, start[person] <= 24 * 60)
    opt.add(end[person] >= 0, end[person] <= 24 * 60)

    # If meeting, obey availability window and minimum duration
    ws = people[person]["window_start"]
    we = people[person]["window_end"]
    md = people[person]["min_duration"]
    loc = people[person]["location"]

    opt.add(Implies(meet[person], And(
        start[person] >= ws,
        end[person] <= we,
        end[person] - start[person] >= md
    )))
    # If not meeting, collapse interval
    opt.add(Implies(If(meet[person], False, True), end[person] == start[person]))

    # Must be reachable from starting location at 09:00
    t0 = travel[(start_location, loc)]
    opt.add(Implies(meet[person], start[person] >= arrival_time + t0))

# No overlap with travel between any pair that are both met
persons = list(people.keys())
for i in range(len(persons)):
    for j in range(i + 1, len(persons)):
        p = persons[i]
        q = persons[j]
        lp = people[p]["location"]
        lq = people[q]["location"]
        tpq = travel[(lp, lq)]
        tqp = travel[(lq, lp)]
        opt.add(Implies(And(meet[p], meet[q]), Or(
            start[q] >= end[p] + tpq,  # p then travel to q
            start[p] >= end[q] + tqp   # q then travel to p
        )))

# Objectives:
# 1) Maximize number of friends met
opt.maximize(Sum([If(meet[p], 1, 0) for p in persons]))
# 2) Maximize total time spent with friends
opt.maximize(Sum([If(meet[p], end[p] - start[p], 0) for p in persons]))
# 3) Tie-breakers to favor intuitive latest feasible adjacency:
#    - End Anthony as late as possible (toward 14:30)
#    - End Melissa as late as possible (push up against travel to Anthony)
if "Anthony" in people:
    opt.maximize(end["Anthony"])
if "Melissa" in people:
    opt.maximize(end["Melissa"])

res = opt.check()
assert str(res) == "sat", "No feasible schedule found"

m = opt.model()

schedule = []
for person in persons:
    if is_true(m[meet[person]]):
        s = m[start[person]].as_long()
        e = m[end[person]].as_long()
        schedule.append({
            "action": "meet",
            "person": person,
            "start_time": mm_to_str(s),
            "end_time": mm_to_str(e)
        })

# Sort by start time
schedule.sort(key=lambda x: x["start_time"])

output = {"itinerary": schedule}
print(json.dumps(output, ensure_ascii=False))