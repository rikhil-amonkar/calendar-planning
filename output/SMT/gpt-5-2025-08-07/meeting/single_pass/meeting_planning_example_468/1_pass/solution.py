# Requires: pip install z3-solver
from z3 import Optimize, Int, Bool, If, Sum
import json

def b2i(b):
    return If(b, 1, 0)

def minutes(h, m):
    return h * 60 + m

def mins_to_hhmm(t):
    h = (t // 60) % 24
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Data
locations = [
    "The Castro",
    "Bayview",
    "Pacific Heights",
    "Alamo Square",
    "Fisherman's Wharf",
    "Golden Gate Park",
]

# Directed travel times (in minutes)
T = {
    "The Castro": {
        "Bayview": 19,
        "Pacific Heights": 16,
        "Alamo Square": 8,
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
    },
    "Bayview": {
        "The Castro": 20,
        "Pacific Heights": 23,
        "Alamo Square": 16,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Bayview": 22,
        "Alamo Square": 10,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15,
    },
    "Alamo Square": {
        "The Castro": 8,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 9,
    },
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Alamo Square": 20,
        "Golden Gate Park": 25,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Alamo Square": 10,
        "Fisherman's Wharf": 24,
    },
}

friends = [
    {
        "person": "Rebecca",
        "loc": "Bayview",
        "avail_start": minutes(9, 0),
        "avail_end": minutes(12, 45),
        "min_dur": 90,
    },
    {
        "person": "Amanda",
        "loc": "Pacific Heights",
        "avail_start": minutes(18, 30),
        "avail_end": minutes(21, 45),
        "min_dur": 90,
    },
    {
        "person": "James",
        "loc": "Alamo Square",
        "avail_start": minutes(9, 45),
        "avail_end": minutes(21, 15),
        "min_dur": 90,
    },
    {
        "person": "Sarah",
        "loc": "Fisherman's Wharf",
        "avail_start": minutes(8, 0),
        "avail_end": minutes(21, 30),
        "min_dur": 90,
    },
    {
        "person": "Melissa",
        "loc": "Golden Gate Park",
        "avail_start": minutes(9, 0),
        "avail_end": minutes(18, 45),
        "min_dur": 90,
    },
]

start_loc = "The Castro"
arrival_time_at_castro = minutes(9, 0)  # 9:00AM

# Z3 Model
opt = Optimize()
opt.set(priority='lex')

M = 100000  # big-M

# Variables
meet = {f["person"]: Bool(f"meet_{f['person']}") for f in friends}
start = {f["person"]: Int(f"start_{f['person']}") for f in friends}
order = {}  # order[p][q] = Bool meaning p scheduled before q
persons = [f["person"] for f in friends]
person_by_name = {f["person"]: f for f in friends}

for i, p in enumerate(persons):
    order[p] = {}
    for j, q in enumerate(persons):
        if p == q:
            continue
        if q in order and p in order[q]:
            continue
        order[p][q] = Bool(f"order_{p}_before_{q}")

# Constraints
for f in friends:
    p = f["person"]
    loc = f["loc"]
    s_av = f["avail_start"]
    e_av = f["avail_end"]
    dur = f["min_dur"]

    # Only constrain times if meeting is chosen
    opt.add(start[p] >= s_av - M * (1 - b2i(meet[p])))
    opt.add(start[p] + dur <= e_av + M * (1 - b2i(meet[p])))

    # Must be reachable from starting point at 9:00
    opt.add(start[p] >= arrival_time_at_castro + T[start_loc][loc] - M * (1 - b2i(meet[p])))

# Pairwise non-overlap and travel sequencing
for i in range(len(persons)):
    for j in range(i + 1, len(persons)):
        p = persons[i]
        q = persons[j]
        loc_p = person_by_name[p]["loc"]
        loc_q = person_by_name[q]["loc"]
        dur_p = person_by_name[p]["min_dur"]
        dur_q = person_by_name[q]["min_dur"]

        # If both are met, then either p before q or q before p with travel times
        ord_pq = order[p][q]
        # q starts after p finishes and travel p->q
        opt.add(
            start[q] >= start[p] + dur_p + T[loc_p][loc_q]
            - M * (1 - b2i(ord_pq))
            - M * (1 - b2i(meet[p]))
            - M * (1 - b2i(meet[q]))
        )
        # p starts after q finishes and travel q->p
        opt.add(
            start[p] >= start[q] + dur_q + T[loc_q][loc_p]
            - M * b2i(ord_pq)
            - M * (1 - b2i(meet[p]))
            - M * (1 - b2i(meet[q]))
        )

# Objective: maximize number of friends met
opt.maximize(Sum([b2i(meet[p]) for p in persons]))
# Tie-breaker: minimize sum of start times for the meetings we do take (to push meetings earlier)
opt.minimize(Sum([If(meet[p], start[p], 0) for p in persons]))

# Solve
if opt.check() != None:
    model = opt.model()
    plan = []
    for p in persons:
        if model.eval(meet[p], model_completion=True):
            st = model.eval(start[p], model_completion=True).as_long()
            et = st + person_by_name[p]["min_dur"]
            plan.append({
                "action": "meet",
                "person": p,
                "start_time": mins_to_hhmm(st),
                "end_time": mins_to_hhmm(et),
            })
    # Sort by start time
    plan.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": plan}, ensure_ascii=False))
else:
    print(json.dumps({"itinerary": []}, ensure_ascii=False))