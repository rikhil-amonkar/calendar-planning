import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat, is_true

def minutes(h, m=0):
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "The Castro",
    "Marina District",
    "Presidio",
    "North Beach",
    "Embarcadero",
    "Haight-Ashbury",
    "Golden Gate Park",
    "Richmond District",
    "Alamo Square",
    "Financial District",
    "Sunset District",
]

# Travel times (minutes). Asymmetric allowed.
travel = {loc: {} for loc in locations}
def add(a, b, t):
    travel[a][b] = t

# Initialize self-travel as 0
for a in locations:
    for b in locations:
        if a == b:
            travel[a][b] = 0

# Fill travel times as provided
add("The Castro", "Marina District", 21)
add("The Castro", "Presidio", 20)
add("The Castro", "North Beach", 20)
add("The Castro", "Embarcadero", 22)
add("The Castro", "Haight-Ashbury", 6)
add("The Castro", "Golden Gate Park", 11)
add("The Castro", "Richmond District", 16)
add("The Castro", "Alamo Square", 8)
add("The Castro", "Financial District", 21)
add("The Castro", "Sunset District", 17)

add("Marina District", "The Castro", 22)
add("Marina District", "Presidio", 10)
add("Marina District", "North Beach", 11)
add("Marina District", "Embarcadero", 14)
add("Marina District", "Haight-Ashbury", 16)
add("Marina District", "Golden Gate Park", 18)
add("Marina District", "Richmond District", 11)
add("Marina District", "Alamo Square", 15)
add("Marina District", "Financial District", 17)
add("Marina District", "Sunset District", 19)

add("Presidio", "The Castro", 21)
add("Presidio", "Marina District", 11)
add("Presidio", "North Beach", 18)
add("Presidio", "Embarcadero", 20)
add("Presidio", "Haight-Ashbury", 15)
add("Presidio", "Golden Gate Park", 12)
add("Presidio", "Richmond District", 7)
add("Presidio", "Alamo Square", 19)
add("Presidio", "Financial District", 23)
add("Presidio", "Sunset District", 15)

add("North Beach", "The Castro", 23)
add("North Beach", "Marina District", 9)
add("North Beach", "Presidio", 17)
add("North Beach", "Embarcadero", 6)
add("North Beach", "Haight-Ashbury", 18)
add("North Beach", "Golden Gate Park", 22)
add("North Beach", "Richmond District", 18)
add("North Beach", "Alamo Square", 16)
add("North Beach", "Financial District", 8)
add("North Beach", "Sunset District", 27)

add("Embarcadero", "The Castro", 25)
add("Embarcadero", "Marina District", 12)
add("Embarcadero", "Presidio", 20)
add("Embarcadero", "North Beach", 5)
add("Embarcadero", "Haight-Ashbury", 21)
add("Embarcadero", "Golden Gate Park", 25)
add("Embarcadero", "Richmond District", 21)
add("Embarcadero", "Alamo Square", 19)
add("Embarcadero", "Financial District", 5)
add("Embarcadero", "Sunset District", 30)

add("Haight-Ashbury", "The Castro", 6)
add("Haight-Ashbury", "Marina District", 17)
add("Haight-Ashbury", "Presidio", 15)
add("Haight-Ashbury", "North Beach", 19)
add("Haight-Ashbury", "Embarcadero", 20)
add("Haight-Ashbury", "Golden Gate Park", 7)
add("Haight-Ashbury", "Richmond District", 10)
add("Haight-Ashbury", "Alamo Square", 5)
add("Haight-Ashbury", "Financial District", 21)
add("Haight-Ashbury", "Sunset District", 15)

add("Golden Gate Park", "The Castro", 13)
add("Golden Gate Park", "Marina District", 16)
add("Golden Gate Park", "Presidio", 11)
add("Golden Gate Park", "North Beach", 23)
add("Golden Gate Park", "Embarcadero", 25)
add("Golden Gate Park", "Haight-Ashbury", 7)
add("Golden Gate Park", "Richmond District", 7)
add("Golden Gate Park", "Alamo Square", 9)
add("Golden Gate Park", "Financial District", 26)
add("Golden Gate Park", "Sunset District", 10)

add("Richmond District", "The Castro", 16)
add("Richmond District", "Marina District", 9)
add("Richmond District", "Presidio", 7)
add("Richmond District", "North Beach", 17)
add("Richmond District", "Embarcadero", 19)
add("Richmond District", "Haight-Ashbury", 10)
add("Richmond District", "Golden Gate Park", 9)
add("Richmond District", "Alamo Square", 13)
add("Richmond District", "Financial District", 22)
add("Richmond District", "Sunset District", 11)

add("Alamo Square", "The Castro", 8)
add("Alamo Square", "Marina District", 15)
add("Alamo Square", "Presidio", 17)
add("Alamo Square", "North Beach", 15)
add("Alamo Square", "Embarcadero", 16)
add("Alamo Square", "Haight-Ashbury", 5)
add("Alamo Square", "Golden Gate Park", 9)
add("Alamo Square", "Richmond District", 11)
add("Alamo Square", "Financial District", 17)
add("Alamo Square", "Sunset District", 16)

add("Financial District", "The Castro", 20)
add("Financial District", "Marina District", 15)
add("Financial District", "Presidio", 22)
add("Financial District", "North Beach", 7)
add("Financial District", "Embarcadero", 4)
add("Financial District", "Haight-Ashbury", 19)
add("Financial District", "Golden Gate Park", 23)
add("Financial District", "Richmond District", 21)
add("Financial District", "Alamo Square", 17)
add("Financial District", "Sunset District", 30)

add("Sunset District", "The Castro", 17)
add("Sunset District", "Marina District", 21)
add("Sunset District", "Presidio", 16)
add("Sunset District", "North Beach", 28)
add("Sunset District", "Embarcadero", 30)
add("Sunset District", "Haight-Ashbury", 15)
add("Sunset District", "Golden Gate Park", 11)
add("Sunset District", "Richmond District", 12)
add("Sunset District", "Alamo Square", 17)
add("Sunset District", "Financial District", 30)

# Friends and constraints
friends = [
    {"person": "Elizabeth", "location": "Marina District", "start": minutes(19, 0), "end": minutes(20, 45), "min_duration": 105},
    {"person": "Joshua", "location": "Presidio", "start": minutes(8, 30), "end": minutes(13, 15), "min_duration": 105},
    {"person": "Timothy", "location": "North Beach", "start": minutes(19, 45), "end": minutes(22, 0), "min_duration": 90},
    {"person": "David", "location": "Embarcadero", "start": minutes(10, 45), "end": minutes(12, 30), "min_duration": 30},
    {"person": "Kimberly", "location": "Haight-Ashbury", "start": minutes(16, 45), "end": minutes(21, 30), "min_duration": 75},
    {"person": "Lisa", "location": "Golden Gate Park", "start": minutes(17, 30), "end": minutes(21, 45), "min_duration": 45},
    {"person": "Ronald", "location": "Richmond District", "start": minutes(8, 0), "end": minutes(9, 30), "min_duration": 90},
    {"person": "Stephanie", "location": "Alamo Square", "start": minutes(15, 30), "end": minutes(16, 30), "min_duration": 30},
    {"person": "Helen", "location": "Financial District", "start": minutes(17, 30), "end": minutes(18, 30), "min_duration": 45},
    {"person": "Laura", "location": "Sunset District", "start": minutes(17, 45), "end": minutes(21, 15), "min_duration": 90},
]

origin = "The Castro"
arrival_time_at_origin = minutes(9, 0)
DAY_START = 0
DAY_END = 24 * 60

opt = Optimize()
# Ensure we maximize number of meetings first, then total duration
opt.set(priority="lex")

meet = {}
start = {}
end = {}

for f in friends:
    name = f["person"]
    meet[name] = Bool(f"meet_{name}")
    start[name] = Int(f"start_{name}")
    end[name] = Int(f"end_{name}")
    # Bounds on times
    opt.add(start[name] >= DAY_START, start[name] <= DAY_END)
    opt.add(end[name] >= DAY_START, end[name] <= DAY_END)
    opt.add(start[name] <= end[name])

    # Availability and minimum duration if meeting
    opt.add(Implies(meet[name], And(
        start[name] >= f["start"],
        end[name] <= f["end"],
        end[name] - start[name] >= f["min_duration"]
    )))

# Pairwise non-overlap with travel-time ordering
for i, fi in enumerate(friends):
    ni = fi["person"]
    li = fi["location"]
    for j, fj in enumerate(friends):
        if i >= j:
            continue
        nj = fj["person"]
        lj = fj["location"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        opt.add(Implies(And(meet[ni], meet[nj]),
                        Or(end[ni] + tij <= start[nj],
                           end[nj] + tji <= start[ni])))

# Reachability from origin or from a predecessor (to ensure a connected, feasible route)
for i, fi in enumerate(friends):
    ni = fi["person"]
    li = fi["location"]
    preds = []
    # From origin
    preds.append(start[ni] >= arrival_time_at_origin + travel[origin][li])
    # From any other meeting
    for j, fj in enumerate(friends):
        if i == j:
            continue
        nj = fj["person"]
        lj = fj["location"]
        preds.append(And(meet[nj], end[nj] + travel[lj][li] <= start[ni]))
    opt.add(Implies(meet[ni], Or(*preds)))

# Objective: maximize number of meetings, then maximize total meeting time
num_meetings = Sum([If(meet[f["person"]], 1, 0) for f in friends])
total_meeting_duration = Sum([If(meet[f["person"]], end[f["person"]] - start[f["person"]], 0) for f in friends])
opt.maximize(num_meetings)
opt.maximize(total_meeting_duration)

# Solve
if opt.check() != sat:
    # No feasible schedule, output empty itinerary
    print(json.dumps({"itinerary": []}, indent=2))
else:
    model = opt.model()
    events = []
    for f in friends:
        name = f["person"]
        if is_true(model.evaluate(meet[name], model_completion=True)):
            s = model.evaluate(start[name]).as_long()
            e = model.evaluate(end[name]).as_long()
            events.append({
                "action": "meet",
                "location": f["location"],
                "person": name,
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e),
                "start_minutes": s  # temporary for sorting
            })
    # Sort by start time
    events.sort(key=lambda x: x["start_minutes"])
    # Remove helper field
    for ev in events:
        del ev["start_minutes"]
    print(json.dumps({"itinerary": events}, indent=2))