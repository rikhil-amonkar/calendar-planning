import json
from z3 import Optimize, Int, Bool, And, Or, Implies, If, Sum

def time_to_min(t):
    # t in "HH:MM" 24-hour format
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Locations
FW = "Fisherman's Wharf"
CASTRO = "The Castro"
GGP = "Golden Gate Park"
EMB = "Embarcadero"
RH = "Russian Hill"
NH = "Nob Hill"
ASQ = "Alamo Square"
NB = "North Beach"

# Travel times in minutes (directed)
travel = {
    (FW, CASTRO): 26, (FW, GGP): 25, (FW, EMB): 8, (FW, RH): 7, (FW, NH): 11, (FW, ASQ): 20, (FW, NB): 6,
    (CASTRO, FW): 24, (CASTRO, GGP): 11, (CASTRO, EMB): 22, (CASTRO, RH): 18, (CASTRO, NH): 16, (CASTRO, ASQ): 8, (CASTRO, NB): 20,
    (GGP, FW): 24, (GGP, CASTRO): 13, (GGP, EMB): 25, (GGP, RH): 19, (GGP, NH): 20, (GGP, ASQ): 10, (GGP, NB): 24,
    (EMB, FW): 6, (EMB, CASTRO): 25, (EMB, GGP): 25, (EMB, RH): 8, (EMB, NH): 10, (EMB, ASQ): 19, (EMB, NB): 5,
    (RH, FW): 7, (RH, CASTRO): 21, (RH, GGP): 21, (RH, EMB): 8, (RH, NH): 5, (RH, ASQ): 15, (RH, NB): 5,
    (NH, FW): 11, (NH, CASTRO): 17, (NH, GGP): 17, (NH, EMB): 9, (NH, RH): 5, (NH, ASQ): 11, (NH, NB): 8,
    (ASQ, FW): 19, (ASQ, CASTRO): 8, (ASQ, GGP): 9, (ASQ, EMB): 17, (ASQ, RH): 13, (ASQ, NH): 11, (ASQ, NB): 15,
    (NB, FW): 5, (NB, CASTRO): 22, (NB, GGP): 22, (NB, EMB): 6, (NB, RH): 4, (NB, NH): 7, (NB, ASQ): 16,
}

# Friends data: location, availability window (24h), minimum meeting duration
friends = {
    "Laura":    {"loc": CASTRO, "start": time_to_min("19:45"), "end": time_to_min("21:30"), "min_dur": 105},
    "Daniel":   {"loc": GGP,    "start": time_to_min("21:15"), "end": time_to_min("21:45"), "min_dur": 15},
    "William":  {"loc": EMB,    "start": time_to_min("07:00"), "end": time_to_min("09:00"), "min_dur": 90},
    "Karen":    {"loc": RH,     "start": time_to_min("14:30"), "end": time_to_min("19:45"), "min_dur": 30},
    "Stephanie":{"loc": NH,     "start": time_to_min("07:30"), "end": time_to_min("09:30"), "min_dur": 45},
    "Joseph":   {"loc": ASQ,    "start": time_to_min("11:30"), "end": time_to_min("12:45"), "min_dur": 15},
    "Kimberly": {"loc": NB,     "start": time_to_min("15:45"), "end": time_to_min("19:15"), "min_dur": 30},
}

start_time_fw = time_to_min("09:00")

opt = Optimize()
opt.set(priority='lex')

start_vars = {}
meet_bools = {}
durations = {}

for person, info in friends.items():
    start_vars[person] = Int(f"start_{person}")
    meet_bools[person] = Bool(f"meet_{person}")
    durations[person] = info["min_dur"]
    # Window constraints if meeting
    opt.add(Implies(
        meet_bools[person],
        And(
            start_vars[person] >= info["start"],
            start_vars[person] + durations[person] <= info["end"]
        )
    ))
    # Reachability from initial location (weak lower bound; ensures not before travel from start)
    # This never binds in this instance but is a reasonable feasibility constraint.
    opt.add(Implies(
        meet_bools[person],
        start_vars[person] >= start_time_fw + travel[(FW, info["loc"])]
    ))

# Pairwise disjunctive scheduling with travel
people = list(friends.keys())
for i in range(len(people)):
    for j in range(i+1, len(people)):
        p_i = people[i]
        p_j = people[j]
        loc_i = friends[p_i]["loc"]
        loc_j = friends[p_j]["loc"]
        dur_i = durations[p_i]
        dur_j = durations[p_j]
        t_ij = travel[(loc_i, loc_j)]
        t_ji = travel[(loc_j, loc_i)]
        opt.add(Implies(
            And(meet_bools[p_i], meet_bools[p_j]),
            Or(
                start_vars[p_i] + dur_i + t_ij <= start_vars[p_j],
                start_vars[p_j] + dur_j + t_ji <= start_vars[p_i]
            )
        ))

# Objectives:
# 1) Maximize number of friends met
num_met = Sum([If(meet_bools[p], 1, 0) for p in people])
opt.maximize(num_met)

# 2) Break ties by maximizing total meeting time (prefers longer meetings like Laura's)
total_meeting_minutes = Sum([If(meet_bools[p], durations[p], 0) for p in people])
opt.maximize(total_meeting_minutes)

# Solve
if opt.check() != sat:
    print("SOLUTION:" + json.dumps({"itinerary": []}))
else:
    model = opt.model()
    chosen = []
    for p in people:
        if model.evaluate(meet_bools[p]):
            s = model.evaluate(start_vars[p]).as_long()
            e = s + durations[p]
            chosen.append({
                "person": p,
                "start": s,
                "end": e
            })
    # Sort by start time
    chosen.sort(key=lambda x: x["start"])
    itinerary = []
    for c in chosen:
        itinerary.append({
            "action": "meet",
            "person": c["person"],
            "start_time": min_to_time(c["start"]),
            "end_time": min_to_time(c["end"])
        })
    print("SOLUTION:" + json.dumps({"itinerary": itinerary}))