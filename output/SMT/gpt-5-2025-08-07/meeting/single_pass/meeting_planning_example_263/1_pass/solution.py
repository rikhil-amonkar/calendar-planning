# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

def minutes(h, m):
    return h*60 + m

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Data
start_location = "Bayview"
start_time = minutes(9, 0)  # 09:00

# Travel times (minutes), asymmetric
T = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Financial District"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10
}

def travel(frm, to):
    return T[(frm, to)]

# Friends data: name, location, [avail_start, avail_end], min_duration
friends = [
    {
        "name": "Betty",
        "loc": "Embarcadero",
        "window": (minutes(19,45), minutes(21,45)),
        "min_dur": 15
    },
    {
        "name": "Karen",
        "loc": "Fisherman's Wharf",
        "window": (minutes(8,45), minutes(15,0)),
        "min_dur": 30
    },
    {
        "name": "Anthony",
        "loc": "Financial District",
        "window": (minutes(9,15), minutes(21,30)),
        "min_dur": 105
    }
]

# Z3 model
opt = Optimize()
opt.set(priority="lex")

S = {}   # start times
E = {}   # end times
Meet = {} # meet decision (Bool)
names = [f["name"] for f in friends]
name_to_friend = {f["name"]: f for f in friends}

for f in friends:
    n = f["name"]
    S[n] = Int(f"S_{n}")
    E[n] = Int(f"E_{n}")
    Meet[n] = Bool(f"Meet_{n}")
    avail_start, avail_end = f["window"]
    min_dur = f["min_dur"]

    # Domain
    opt.add(S[n] >= 0, E[n] >= 0, E[n] >= S[n])

    # Availability and duration constraints when meeting
    opt.add(Implies(Meet[n], And(
        S[n] >= avail_start,
        E[n] <= avail_end,
        E[n] - S[n] >= min_dur
    )))
    # If not meeting, no time spent (collapse interval)
    opt.add(Implies(Not(Meet[n]), E[n] == S[n]))

    # Must be able to get from Bayview at 09:00 to the meeting location (lower bound)
    opt.add(Implies(Meet[n], S[n] >= start_time + travel(start_location, f["loc"])))

# Disjunctive non-overlap with travel between meetings
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        fi = friends[i]
        fj = friends[j]
        ni, nj = fi["name"], fj["name"]
        ti2j = travel(fi["loc"], fj["loc"])
        tj2i = travel(fj["loc"], fi["loc"])
        # If both are met, either i before j (with travel) or j before i (with travel)
        opt.add(Implies(And(Meet[ni], Meet[nj]),
                        Or(E[ni] + ti2j <= S[nj],
                           E[nj] + tj2i <= S[ni])))

# Objective 1: maximize number of friends met
total_met = Sum([If(Meet[n], 1, 0) for n in names])
opt.maximize(total_met)

# Objective 2: minimize the latest end time among meetings (compact day)
LastEnd = Int("LastEnd")
opt.add(LastEnd >= 0)
for n in names:
    opt.add(LastEnd >= E[n])
opt.minimize(LastEnd)

# Objective 3 (tie-breaker): minimize earliest start (encourage earlier starts)
EarliestStart = Int("EarliestStart")
opt.add(EarliestStart >= 0)
for n in names:
    # If not met, S[n] == E[n], but we still minimize the min over all S's. That's fine.
    pass
# Model min(S[n]) via upper-bounds and minimize EarliestStart
for n in names:
    opt.add(EarliestStart <= S[n])
# Also bound it from below by actual minimum possible start (from Bayview to nearest location)
opt.add(EarliestStart >= start_time)  # can't start before 09:00
opt.minimize(EarliestStart)

res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    meetings = []
    for f in friends:
        n = f["name"]
        if is_true(m[Meet[n]]):
            st = m[S[n]].as_long()
            en = m[E[n]].as_long()
            meetings.append({
                "action": "meet",
                "person": n,
                "start_time": minutes_to_hhmm(st),
                "end_time": minutes_to_hhmm(en)
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": meetings}, ensure_ascii=False))