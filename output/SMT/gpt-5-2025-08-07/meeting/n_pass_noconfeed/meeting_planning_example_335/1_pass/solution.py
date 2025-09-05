import json
from z3 import *

def time_to_min(h, m):
    return h * 60 + m

def min_to_time_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Define locations
PH = "Pacific Heights"
NB = "North Beach"
FD = "Financial District"
AS = "Alamo Square"
MD = "Mission District"

locations = [PH, NB, FD, AS, MD]

# Travel times (minutes), directional
travel = {
    PH: {NB: 9,  FD: 13, AS: 10, MD: 15},
    NB: {PH: 8,  FD: 8,  AS: 16, MD: 18},
    FD: {PH: 13, NB: 7,  AS: 17, MD: 17},
    AS: {PH: 10, NB: 15, FD: 17, MD: 10},
    MD: {PH: 16, NB: 17, FD: 17, AS: 11},
}
# Add zero self-travel and ensure dict completeness for all pairs
for a in locations:
    if a not in travel:
        travel[a] = {}
    for b in locations:
        if a == b:
            travel[a][b] = 0
        else:
            if b not in travel[a]:
                # If any missing (shouldn't be), set a large number to discourage it
                travel[a][b] = 10**6

# People data: name, location, availability window (minutes since midnight), min duration
people = [
    {
        "name": "Helen",
        "location": NB,
        "avail_start": time_to_min(9, 0),
        "avail_end": time_to_min(17, 0),
        "min_duration": 15
    },
    {
        "name": "Betty",
        "location": FD,
        "avail_start": time_to_min(19, 0),
        "avail_end": time_to_min(21, 45),
        "min_duration": 90
    },
    {
        "name": "Amanda",
        "location": AS,
        "avail_start": time_to_min(19, 45),
        "avail_end": time_to_min(21, 0),
        "min_duration": 60
    },
    {
        "name": "Kevin",
        "location": MD,
        "avail_start": time_to_min(10, 45),
        "avail_end": time_to_min(14, 45),
        "min_duration": 45
    },
]

day_start = time_to_min(9, 0)
start_location = PH

opt = Optimize()

# Variables for each person
vars_map = {}
for p in people:
    meet = Bool(f"meet_{p['name']}")
    start = Int(f"start_{p['name']}")
    dur = Int(f"dur_{p['name']}")
    end = Int(f"end_{p['name']}")
    vars_map[p['name']] = {"meet": meet, "start": start, "dur": dur, "end": end}

    # Basic domains
    opt.add(start >= 0)
    opt.add(dur >= 0)
    opt.add(end == start + dur)

    # If meeting, enforce availability and minimum duration and earliest arrival from start
    opt.add(Implies(meet, And(
        start >= p["avail_start"],
        end <= p["avail_end"],
        dur >= p["min_duration"],
        start >= day_start + travel[start_location][p["location"]]
    )))

# Non-overlap with travel-time separation between meetings
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        pi = people[i]
        pj = people[j]
        vi = vars_map[pi["name"]]
        vj = vars_map[pj["name"]]
        # If both meetings occur, then either i before j with travel or j before i with travel
        opt.add(Implies(And(vi["meet"], vj["meet"]),
                        Or(
                            vi["end"] + travel[pi["location"]][pj["location"]] <= vj["start"],
                            vj["end"] + travel[pj["location"]][pi["location"]] <= vi["start"]
                        )))

# Objectives: maximize number of meetings, then maximize total meeting time
total_meetings = Sum([If(vars_map[p["name"]]["meet"], 1, 0) for p in people])
total_minutes = Sum([If(vars_map[p["name"]]["meet"], vars_map[p["name"]]["dur"], 0) for p in people])

opt.maximize(total_meetings)
opt.maximize(total_minutes)

if opt.check() != sat:
    # If unsat (shouldn't happen), output empty itinerary
    result = {"itinerary": []}
    print(json.dumps(result))
    exit(0)

model = opt.model()

# Build itinerary from model
itinerary = []
for p in people:
    v = vars_map[p["name"]]
    if is_true(model.evaluate(v["meet"], model_completion=True)):
        start_val = model.evaluate(v["start"], model_completion=True).as_long()
        end_val = model.evaluate(v["end"], model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": min_to_time_str(start_val),
            "end_time": min_to_time_str(end_val)
        })

# Sort by start time
itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))