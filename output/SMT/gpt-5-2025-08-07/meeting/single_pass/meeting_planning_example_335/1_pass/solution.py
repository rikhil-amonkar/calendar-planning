# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum
import json

def hm(h, m):
    return h * 60 + m

def mm_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Locations
PH = "Pacific Heights"
NB = "North Beach"
FD = "Financial District"
AS = "Alamo Square"
MD = "Mission District"

# Directed travel times (minutes)
travel = {
    PH: {NB: 9,  FD: 13, AS: 10, MD: 15},
    NB: {PH: 8,  FD: 8,  AS: 16, MD: 18},
    FD: {PH: 13, NB: 7,  AS: 17, MD: 17},
    AS: {PH: 10, NB: 15, FD: 17, MD: 10},
    MD: {PH: 16, NB: 17, FD: 17, AS: 11},
}

# People data: location, availability window, and minimum meeting time
people = {
    "Helen":  {"loc": NB, "start": hm(9, 0),  "end": hm(17, 0), "min": 15},
    "Betty":  {"loc": FD, "start": hm(19, 0), "end": hm(21, 45), "min": 90},
    "Amanda": {"loc": AS, "start": hm(19, 45),"end": hm(21, 0),  "min": 60},
    "Kevin":  {"loc": MD, "start": hm(10,45), "end": hm(14,45), "min": 45},
}

day_start_loc = PH
day_start_time = hm(9, 0)

# Z3 model
opt = Optimize()
opt.set(priority='lex')

meet = {}
start = {}
end = {}

# Variables and constraints per person
for p, info in people.items():
    meet[p] = Bool(f"meet_{p}")
    start[p] = Int(f"start_{p}")
    end[p] = Int(f"end_{p}")

    # Bounds on times
    opt.add(start[p] >= 0, end[p] >= 0, end[p] <= hm(23,59))

    # If meeting, times within availability and minimum duration
    opt.add(If(meet[p],
               And(start[p] >= info["start"],
                   end[p]   <= info["end"],
                   end[p] - start[p] >= info["min"],
                   start[p] < end[p]),
               True))

    # Reachability from starting point
    loc = info["loc"]
    opt.add(If(meet[p],
               start[p] >= day_start_time + travel[day_start_loc][loc],
               True))

# No-overlap + travel between any two meetings
persons = list(people.keys())
for i in range(len(persons)):
    for j in range(i+1, len(persons)):
        pi, pj = persons[i], persons[j]
        li, lj = people[pi]["loc"], people[pj]["loc"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        opt.add(If(And(meet[pi], meet[pj]),
                   Or(end[pi] + tij <= start[pj],
                      end[pj] + tji <= start[pi]]),
                   True))

# Objectives:
# 1) Maximize number of friends met
num_met = Sum([If(meet[p], 1, 0) for p in persons])
opt.maximize(num_met)

# 2) Tie-breaker: maximize total meeting time (encourages fuller meetings; still respects windows)
total_meeting_minutes = Sum([If(meet[p], end[p] - start[p], 0) for p in persons])
opt.maximize(total_meeting_minutes)

# Solve
if opt.check() != 1:
    raise RuntimeError("No feasible schedule found")

m = opt.model()

# Build itinerary sorted by start time
meetings = []
for p in persons:
    if m.evaluate(meet[p]).is_true():
        s = m.evaluate(start[p]).as_long()
        e = m.evaluate(end[p]).as_long()
        meetings.append((s, {
            "action": "meet",
            "person": p,
            "start_time": mm_to_str(s),
            "end_time": mm_to_str(e)
        }))

meetings.sort(key=lambda x: x[0])
itinerary = [entry for _, entry in meetings]

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))