from z3 import Optimize, Int, Bool, If, And, Or, Not, Implies, Xor, Sum, sat
import json

# Minutes helper
def hm_to_min(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Problem data
locations = [
    "Sunset District",
    "Presidio",
    "Nob Hill",
    "Pacific Heights",
    "Mission District",
    "Marina District",
    "North Beach",
    "Russian Hill",
    "Richmond District",
    "Embarcadero",
    "Alamo Square",
]

# Directed travel times (minutes)
tt = {}
def set_tt(fr, to, val):
    tt[(fr, to)] = val

# Sunset District row
set_tt("Sunset District", "Presidio", 16)
set_tt("Sunset District", "Nob Hill", 27)
set_tt("Sunset District", "Pacific Heights", 21)
set_tt("Sunset District", "Mission District", 25)
set_tt("Sunset District", "Marina District", 21)
set_tt("Sunset District", "North Beach", 28)
set_tt("Sunset District", "Russian Hill", 24)
set_tt("Sunset District", "Richmond District", 12)
set_tt("Sunset District", "Embarcadero", 30)
set_tt("Sunset District", "Alamo Square", 17)

# Presidio row
set_tt("Presidio", "Sunset District", 15)
set_tt("Presidio", "Nob Hill", 18)
set_tt("Presidio", "Pacific Heights", 11)
set_tt("Presidio", "Mission District", 26)
set_tt("Presidio", "Marina District", 11)
set_tt("Presidio", "North Beach", 18)
set_tt("Presidio", "Russian Hill", 14)
set_tt("Presidio", "Richmond District", 7)
set_tt("Presidio", "Embarcadero", 20)
set_tt("Presidio", "Alamo Square", 19)

# Nob Hill row
set_tt("Nob Hill", "Sunset District", 24)
set_tt("Nob Hill", "Presidio", 17)
set_tt("Nob Hill", "Pacific Heights", 8)
set_tt("Nob Hill", "Mission District", 13)
set_tt("Nob Hill", "Marina District", 11)
set_tt("Nob Hill", "North Beach", 8)
set_tt("Nob Hill", "Russian Hill", 5)
set_tt("Nob Hill", "Richmond District", 14)
set_tt("Nob Hill", "Embarcadero", 9)
set_tt("Nob Hill", "Alamo Square", 11)

# Pacific Heights row
set_tt("Pacific Heights", "Sunset District", 21)
set_tt("Pacific Heights", "Presidio", 11)
set_tt("Pacific Heights", "Nob Hill", 8)
set_tt("Pacific Heights", "Mission District", 15)
set_tt("Pacific Heights", "Marina District", 6)
set_tt("Pacific Heights", "North Beach", 9)
set_tt("Pacific Heights", "Russian Hill", 7)
set_tt("Pacific Heights", "Richmond District", 12)
set_tt("Pacific Heights", "Embarcadero", 10)
set_tt("Pacific Heights", "Alamo Square", 10)

# Mission District row
set_tt("Mission District", "Sunset District", 24)
set_tt("Mission District", "Presidio", 25)
set_tt("Mission District", "Nob Hill", 12)
set_tt("Mission District", "Pacific Heights", 16)
set_tt("Mission District", "Marina District", 19)
set_tt("Mission District", "North Beach", 17)
set_tt("Mission District", "Russian Hill", 15)
set_tt("Mission District", "Richmond District", 20)
set_tt("Mission District", "Embarcadero", 19)
set_tt("Mission District", "Alamo Square", 11)

# Marina District row
set_tt("Marina District", "Sunset District", 19)
set_tt("Marina District", "Presidio", 10)
set_tt("Marina District", "Nob Hill", 12)
set_tt("Marina District", "Pacific Heights", 7)
set_tt("Marina District", "Mission District", 20)
set_tt("Marina District", "North Beach", 11)
set_tt("Marina District", "Russian Hill", 8)
set_tt("Marina District", "Richmond District", 11)
set_tt("Marina District", "Embarcadero", 14)
set_tt("Marina District", "Alamo Square", 15)

# North Beach row
set_tt("North Beach", "Sunset District", 27)
set_tt("North Beach", "Presidio", 17)
set_tt("North Beach", "Nob Hill", 7)
set_tt("North Beach", "Pacific Heights", 8)
set_tt("North Beach", "Mission District", 18)
set_tt("North Beach", "Marina District", 9)
set_tt("North Beach", "Russian Hill", 4)
set_tt("North Beach", "Richmond District", 18)
set_tt("North Beach", "Embarcadero", 6)
set_tt("North Beach", "Alamo Square", 16)

# Russian Hill row
set_tt("Russian Hill", "Sunset District", 23)
set_tt("Russian Hill", "Presidio", 14)
set_tt("Russian Hill", "Nob Hill", 5)
set_tt("Russian Hill", "Pacific Heights", 7)
set_tt("Russian Hill", "Mission District", 16)
set_tt("Russian Hill", "Marina District", 7)
set_tt("Russian Hill", "North Beach", 5)
set_tt("Russian Hill", "Richmond District", 13)
set_tt("Russian Hill", "Embarcadero", 8)
set_tt("Russian Hill", "Alamo Square", 15)

# Richmond District row
set_tt("Richmond District", "Sunset District", 11)
set_tt("Richmond District", "Presidio", 7)
set_tt("Richmond District", "Nob Hill", 17)
set_tt("Richmond District", "Pacific Heights", 10)
set_tt("Richmond District", "Mission District", 20)
set_tt("Richmond District", "Marina District", 9)
set_tt("Richmond District", "North Beach", 17)
set_tt("Richmond District", "Russian Hill", 13)
set_tt("Richmond District", "Embarcadero", 19)
set_tt("Richmond District", "Alamo Square", 13)

# Embarcadero row
set_tt("Embarcadero", "Sunset District", 30)
set_tt("Embarcadero", "Presidio", 20)
set_tt("Embarcadero", "Nob Hill", 10)
set_tt("Embarcadero", "Pacific Heights", 11)
set_tt("Embarcadero", "Mission District", 20)
set_tt("Embarcadero", "Marina District", 12)
set_tt("Embarcadero", "North Beach", 5)
set_tt("Embarcadero", "Russian Hill", 8)
set_tt("Embarcadero", "Richmond District", 21)
set_tt("Embarcadero", "Alamo Square", 19)

# Alamo Square row
set_tt("Alamo Square", "Sunset District", 16)
set_tt("Alamo Square", "Presidio", 17)
set_tt("Alamo Square", "Nob Hill", 11)
set_tt("Alamo Square", "Pacific Heights", 10)
set_tt("Alamo Square", "Mission District", 10)
set_tt("Alamo Square", "Marina District", 15)
set_tt("Alamo Square", "North Beach", 15)
set_tt("Alamo Square", "Russian Hill", 13)
set_tt("Alamo Square", "Richmond District", 11)
set_tt("Alamo Square", "Embarcadero", 16)

# Same-location travel time is zero
for a in locations:
    tt[(a, a)] = 0

def travel_time(a, b):
    return tt[(a, b)]

start_location = "Sunset District"
start_time = hm_to_min(9, 0)  # 9:00

# Friends and their constraints
friends = {
    "Charles":  {"location": "Presidio",         "avail_start": hm_to_min(13, 15), "avail_end": hm_to_min(15, 0),  "min_dur": 105},
    "Robert":   {"location": "Nob Hill",         "avail_start": hm_to_min(13, 15), "avail_end": hm_to_min(17, 30), "min_dur": 90},
    "Nancy":    {"location": "Pacific Heights",  "avail_start": hm_to_min(14, 45), "avail_end": hm_to_min(22, 0),  "min_dur": 105},
    "Brian":    {"location": "Mission District", "avail_start": hm_to_min(15, 30), "avail_end": hm_to_min(22, 0),  "min_dur": 60},
    "Kimberly": {"location": "Marina District",  "avail_start": hm_to_min(17, 0),  "avail_end": hm_to_min(19, 45), "min_dur": 75},
    "David":    {"location": "North Beach",      "avail_start": hm_to_min(14, 45), "avail_end": hm_to_min(16, 30), "min_dur": 75},
    "William":  {"location": "Russian Hill",     "avail_start": hm_to_min(12, 30), "avail_end": hm_to_min(19, 15), "min_dur": 120},
    "Jeffrey":  {"location": "Richmond District","avail_start": hm_to_min(12, 0),  "avail_end": hm_to_min(19, 15), "min_dur": 45},
    "Karen":    {"location": "Embarcadero",      "avail_start": hm_to_min(14, 15), "avail_end": hm_to_min(20, 45), "min_dur": 60},
    "Joshua":   {"location": "Alamo Square",     "avail_start": hm_to_min(18, 45), "avail_end": hm_to_min(22, 0),  "min_dur": 60},
}

HORIZON_END = hm_to_min(22, 0)

# Z3 variables
opt = Optimize()

meet = {}
start = {}
end = {}
first = {}
people = list(friends.keys())

for p in people:
    meet[p] = Bool(f"meet_{p}")
    first[p] = Bool(f"first_{p}")
    start[p] = Int(f"start_{p}")
    end[p] = Int(f"end_{p}")

# Pairwise ordering booleans
before = {}
for i in range(len(people)):
    for j in range(len(people)):
        if i == j:
            continue
        a = people[i]
        b = people[j]
        before[(a, b)] = Bool(f"before_{a}_{b}")

# Time window constraints per person
for p, info in friends.items():
    a_s = info["avail_start"]
    a_e = info["avail_end"]
    min_d = info["min_dur"]

    opt.add(Implies(meet[p], start[p] >= a_s))
    opt.add(Implies(meet[p], end[p] <= a_e))
    opt.add(Implies(meet[p], end[p] - start[p] >= min_d))
    opt.add(Implies(meet[p], end[p] <= HORIZON_END))
    # If not meeting, we can leave times unconstrained; to keep them sensible:
    opt.add(Implies(Not(meet[p]), And(start[p] == 0, end[p] == 0)))

# Ordering and travel time constraints
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        a = people[i]
        b = people[j]
        # If both met, exactly one ordering must hold
        opt.add(Implies(And(meet[a], meet[b]), Xor(before[(a, b)], before[(b, a)])))
        # If not both met, then neither ordering applies
        opt.add(Implies(Not(And(meet[a], meet[b])), And(Not(before[(a, b)]), Not(before[(b, a)]))))
        # Travel time constraints
        ta = travel_time(friends[a]["location"], friends[b]["location"])
        tb = travel_time(friends[b]["location"], friends[a]["location"])
        opt.add(Implies(And(meet[a], meet[b], before[(a, b)]), start[b] >= end[a] + ta))
        opt.add(Implies(And(meet[a], meet[b], before[(b, a)]), start[a] >= end[b] + tb))

# First meeting constraints
sum_first = Sum([If(first[p], 1, 0) for p in people])
sum_meet = Sum([If(meet[p], 1, 0) for p in people])

# At most one first
opt.add(sum_first <= 1)
# If at least one meeting, exactly one first
opt.add(Or(sum_meet == 0, sum_first == 1))

for p in people:
    # First implies we meet them
    opt.add(Implies(first[p], meet[p]))
    # First implies they're before all others that are met
    for q in people:
        if p == q:
            continue
        opt.add(Implies(And(first[p], meet[q]), before[(p, q)]))
    # Arrival from starting point to the first meeting
    t0 = travel_time(start_location, friends[p]["location"])
    opt.add(Implies(first[p], start[p] >= start_time + t0))

# Objective: maximize number of friends met; as a tiebreaker maximize total meeting time, then minimize makespan end time
total_meeting_time = Sum([If(meet[p], end[p] - start[p], 0) for p in people])
makespan_end = Int("makespan_end")
# makespan_end is the maximum end time among meetings (or start_time if none)
opt.add(makespan_end >= start_time)
for p in people:
    opt.add(makespan_end >= end[p])
# Optimize: maximize count, then maximize total meeting time, then minimize makespan
opt.maximize(sum_meet)
opt.maximize(total_meeting_time)
opt.minimize(makespan_end)

# Solve
if opt.check() != sat:
    # If unsat, output empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    m = opt.model()
    scheduled = []
    for p in people:
        if m.evaluate(meet[p]):
            st = m.evaluate(start[p]).as_long()
            en = m.evaluate(end[p]).as_long()
            scheduled.append({
                "person": p,
                "location": friends[p]["location"],
                "start": st,
                "end": en
            })
    # Sort by start time
    scheduled.sort(key=lambda x: x["start"])
    itinerary = []
    for item in scheduled:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start"]),
            "end_time": minutes_to_str(item["end"])
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))