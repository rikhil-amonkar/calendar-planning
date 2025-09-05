import json
from z3 import Int, Bool, Optimize, If, And, Or, Implies, Sum, sat

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(total):
    h = total // 60
    m = total % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) between locations
locations = [
    "Fisherman's Wharf",
    "The Castro",
    "Golden Gate Park",
    "Embarcadero",
    "Russian Hill",
    "Nob Hill",
    "Alamo Square",
    "North Beach",
]

travel = {loc: {} for loc in locations}
def set_travel(a, b, t):
    travel[a][b] = t

# Initialize same-location travel as 0
for loc in locations:
    travel[loc][loc] = 0

# Given travel times
set_travel("Fisherman's Wharf", "The Castro", 26)
set_travel("Fisherman's Wharf", "Golden Gate Park", 25)
set_travel("Fisherman's Wharf", "Embarcadero", 8)
set_travel("Fisherman's Wharf", "Russian Hill", 7)
set_travel("Fisherman's Wharf", "Nob Hill", 11)
set_travel("Fisherman's Wharf", "Alamo Square", 20)
set_travel("Fisherman's Wharf", "North Beach", 6)

set_travel("The Castro", "Fisherman's Wharf", 24)
set_travel("The Castro", "Golden Gate Park", 11)
set_travel("The Castro", "Embarcadero", 22)
set_travel("The Castro", "Russian Hill", 18)
set_travel("The Castro", "Nob Hill", 16)
set_travel("The Castro", "Alamo Square", 8)
set_travel("The Castro", "North Beach", 20)

set_travel("Golden Gate Park", "Fisherman's Wharf", 24)
set_travel("Golden Gate Park", "The Castro", 13)
set_travel("Golden Gate Park", "Embarcadero", 25)
set_travel("Golden Gate Park", "Russian Hill", 19)
set_travel("Golden Gate Park", "Nob Hill", 20)
set_travel("Golden Gate Park", "Alamo Square", 10)
set_travel("Golden Gate Park", "North Beach", 24)

set_travel("Embarcadero", "Fisherman's Wharf", 6)
set_travel("Embarcadero", "The Castro", 25)
set_travel("Embarcadero", "Golden Gate Park", 25)
set_travel("Embarcadero", "Russian Hill", 8)
set_travel("Embarcadero", "Nob Hill", 10)
set_travel("Embarcadero", "Alamo Square", 19)
set_travel("Embarcadero", "North Beach", 5)

set_travel("Russian Hill", "Fisherman's Wharf", 7)
set_travel("Russian Hill", "The Castro", 21)
set_travel("Russian Hill", "Golden Gate Park", 21)
set_travel("Russian Hill", "Embarcadero", 8)
set_travel("Russian Hill", "Nob Hill", 5)
set_travel("Russian Hill", "Alamo Square", 15)
set_travel("Russian Hill", "North Beach", 5)

set_travel("Nob Hill", "Fisherman's Wharf", 11)
set_travel("Nob Hill", "The Castro", 17)
set_travel("Nob Hill", "Golden Gate Park", 17)
set_travel("Nob Hill", "Embarcadero", 9)
set_travel("Nob Hill", "Russian Hill", 5)
set_travel("Nob Hill", "Alamo Square", 11)
set_travel("Nob Hill", "North Beach", 8)

set_travel("Alamo Square", "Fisherman's Wharf", 19)
set_travel("Alamo Square", "The Castro", 8)
set_travel("Alamo Square", "Golden Gate Park", 9)
set_travel("Alamo Square", "Embarcadero", 17)
set_travel("Alamo Square", "Russian Hill", 13)
set_travel("Alamo Square", "Nob Hill", 11)
set_travel("Alamo Square", "North Beach", 15)

set_travel("North Beach", "Fisherman's Wharf", 5)
set_travel("North Beach", "The Castro", 22)
set_travel("North Beach", "Golden Gate Park", 22)
set_travel("North Beach", "Embarcadero", 6)
set_travel("North Beach", "Russian Hill", 4)
set_travel("North Beach", "Nob Hill", 7)
set_travel("North Beach", "Alamo Square", 16)

# People constraints
people = [
    {"name": "Laura", "location": "The Castro", "start": minutes(19,45), "end": minutes(21,30), "min_dur": 105},
    {"name": "Daniel", "location": "Golden Gate Park", "start": minutes(21,15), "end": minutes(21,45), "min_dur": 15},
    {"name": "William", "location": "Embarcadero", "start": minutes(7,0), "end": minutes(9,0), "min_dur": 90},
    {"name": "Karen", "location": "Russian Hill", "start": minutes(14,30), "end": minutes(19,45), "min_dur": 30},
    {"name": "Stephanie", "location": "Nob Hill", "start": minutes(7,30), "end": minutes(9,30), "min_dur": 45},
    {"name": "Joseph", "location": "Alamo Square", "start": minutes(11,30), "end": minutes(12,45), "min_dur": 15},
    {"name": "Kimberly", "location": "North Beach", "start": minutes(15,45), "end": minutes(19,15), "min_dur": 30},
]

start_location = "Fisherman's Wharf"
arrival_time = minutes(9, 0)

# Z3 variables
opt = Optimize()
vars_data = {}

for p in people:
    s = Int(f"s_{p['name']}")
    e = Int(f"e_{p['name']}")
    meet = Bool(f"meet_{p['name']}")
    vars_data[p['name']] = {"s": s, "e": e, "meet": meet}

    # Bounds for times within the day
    opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)

    # If meeting, enforce availability and minimum duration and feasibility with initial travel from arrival point
    opt.add(Implies(meet, And(
        s >= p["start"],
        e <= p["end"],
        e > s,
        e - s >= p["min_dur"],
        s >= arrival_time + travel[start_location][p["location"]]
    )))

    # If not meeting, collapse interval
    opt.add(Implies(~meet, e == s))

# Pairwise non-overlap with travel time between meetings
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        pi = people[i]
        pj = people[j]
        vi = vars_data[pi["name"]]
        vj = vars_data[pj["name"]]
        ti_j = travel[pi["location"]][pj["location"]]
        tj_i = travel[pj["location"]][pi["location"]]
        opt.add(Implies(And(vi["meet"], vj["meet"]),
                        Or(vi["e"] + ti_j <= vj["s"],
                           vj["e"] + tj_i <= vi["s"])
                        ))

# Objective: maximize number of meetings, tie-breaker maximize total meeting time
meet_count = Sum([If(vars_data[p["name"]]["meet"], 1, 0) for p in people])
total_meeting_time = Sum([If(vars_data[p["name"]]["meet"], vars_data[p["name"]]["e"] - vars_data[p["name"]]["s"], 0) for p in people])
opt.maximize(meet_count)
opt.maximize(total_meeting_time)

result = opt.check()

itinerary = []
if result == sat:
    model = opt.model()
    # Build list of meetings with their times
    events = []
    for p in people:
        v = vars_data[p["name"]]
        if model.eval(v["meet"]).is_true():
            s_val = model.eval(v["s"]).as_long()
            e_val = model.eval(v["e"]).as_long()
            events.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start": s_val,
                "end": e_val
            })
    # Sort by start time
    events.sort(key=lambda x: x["start"])
    for ev in events:
        itinerary.append({
            "action": "meet",
            "location": ev["location"],
            "person": ev["person"],
            "start_time": minutes_to_str(ev["start"]),
            "end_time": minutes_to_str(ev["end"])
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))