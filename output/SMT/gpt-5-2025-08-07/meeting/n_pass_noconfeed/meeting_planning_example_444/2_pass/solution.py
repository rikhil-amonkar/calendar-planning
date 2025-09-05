import json
import sys
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat, is_true

# Basic time helpers
def hm_to_min(h, m):
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
FD = "Financial District"
RH = "Russian Hill"
SD = "Sunset District"
NB = "North Beach"
TC = "The Castro"
GGP = "Golden Gate Park"

# Directed travel times (in minutes)
t = {
    (FD, RH): 10, (FD, SD): 31, (FD, NB): 7,  (FD, TC): 23, (FD, GGP): 23,
    (RH, FD): 11, (RH, SD): 23, (RH, NB): 5,  (RH, TC): 21, (RH, GGP): 21,
    (SD, FD): 30, (SD, RH): 24, (SD, NB): 29, (SD, TC): 17, (SD, GGP): 11,
    (NB, FD): 8,  (NB, RH): 4,  (NB, SD): 27, (NB, TC): 22, (NB, GGP): 22,
    (TC, FD): 20, (TC, RH): 18, (TC, SD): 17, (TC, NB): 20, (TC, GGP): 11,
    (GGP, FD): 26,(GGP, RH): 19,(GGP, SD): 10,(GGP, NB): 24,(GGP, TC): 13,
}

# People, locations, availability windows, and minimum meeting durations
people = [
    {
        "name": "Ronald",
        "location": RH,
        "avail_start": hm_to_min(13,45),
        "avail_end":   hm_to_min(17,15),
        "min_duration": 105
    },
    {
        "name": "Patricia",
        "location": SD,
        "avail_start": hm_to_min(9,15),
        "avail_end":   hm_to_min(22,0),
        "min_duration": 60
    },
    {
        "name": "Laura",
        "location": NB,
        "avail_start": hm_to_min(12,30),
        "avail_end":   hm_to_min(12,45),
        "min_duration": 15
    },
    {
        "name": "Emily",
        "location": TC,
        "avail_start": hm_to_min(16,15),
        "avail_end":   hm_to_min(18,30),
        "min_duration": 60
    },
    {
        "name": "Mary",
        "location": GGP,
        "avail_start": hm_to_min(15,0),
        "avail_end":   hm_to_min(16,30),
        "min_duration": 60
    },
]

start_time = hm_to_min(9,0)  # Arrive at Financial District at 9:00

# Build Z3 model
opt = Optimize()
opt.set(priority='lex')  # 1) maximize count, 2) maximize total duration, 3) tie-breaker

# Variables per person
vars_map = {}
for p in people:
    name = p["name"]
    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    m = Bool(f"m_{name}")
    vars_map[name] = {"s": s, "e": e, "m": m}

    # Basic bounds
    opt.add(s >= 0, e >= 0, e >= s, s <= hm_to_min(23,59), e <= hm_to_min(23,59))

    # Availability and minimum duration if meeting occurs
    opt.add(Implies(m, And(
        s >= p["avail_start"],
        e <= p["avail_end"],
        e - s >= p["min_duration"]
    )))

# Pairwise non-overlap with travel times if both meetings occur
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        vi = vars_map[pi["name"]]
        vj = vars_map[pj["name"]]
        # If meeting both, enforce order with travel
        travel_ij = t[(pi["location"], pj["location"])]
        travel_ji = t[(pj["location"], pi["location"])]
        opt.add(Implies(And(vi["m"], vj["m"]),
                        Or(vi["e"] + travel_ij <= vj["s"],
                           vj["e"] + travel_ji <= vi["s"])))

# Connectivity from start (Financial District at 9:00) or predecessor
# For each meeting p: if m_p, then either reachable directly from start,
# or there exists q (met) that precedes p with travel time.
for i in range(len(people)):
    pi = people[i]
    vi = vars_map[pi["name"]]
    preds = []
    for j in range(len(people)):
        if i == j: 
            continue
        pj = people[j]
        vj = vars_map[pj["name"]]
        preds.append(And(vj["m"], vj["e"] + t[(pj["location"], pi["location"])] <= vi["s"]))
    direct_from_start = (vi["s"] >= start_time + t[(FD, pi["location"])])
    if preds:
        opt.add(Implies(vi["m"], Or(direct_from_start, Or(*preds))))
    else:
        opt.add(Implies(vi["m"], direct_from_start))

# Objectives
meet_count = Sum([If(vars_map[p["name"]]["m"], 1, 0) for p in people])
total_meet_time = Sum([If(vars_map[p["name"]]["m"], vars_map[p["name"]"]["e"] - vars_map[p["name"]]["s"], 0) for p in people])

# Primary: maximize number of people met
opt.maximize(meet_count)
# Secondary: maximize total meeting time
opt.maximize(total_meet_time)
# Tertiary: tie-breaker - prefer earlier start of Emily's meeting (to reduce ambiguity)
opt.minimize(vars_map["Emily"]["s"])

# Solve
res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
    sys.exit(0)

model = opt.model()

# Build itinerary
itinerary = []
for p in people:
    v = vars_map[p["name"]]
    if is_true(model.evaluate(v["m"])):
        s_val = model.evaluate(v["s"]).as_long()
        e_val = model.evaluate(v["e"]).as_long()
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_time(s_val),
            "end_time": fmt_time(e_val)
        })

# Sort by start time
itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

print(json.dumps({"itinerary": itinerary}, ensure_ascii=True))