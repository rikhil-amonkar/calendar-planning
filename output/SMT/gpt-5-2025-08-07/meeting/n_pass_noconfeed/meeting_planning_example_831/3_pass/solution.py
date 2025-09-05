# SOLUTION (revised, fixed):
import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat, is_true

# Helper to parse times like '10:15AM' or '5:45PM' into minutes since midnight
def parse_time(t):
    t = t.strip().upper()
    if t.endswith("AM") or t.endswith("PM"):
        ampm = t[-2:]
        hm = t[:-2]
    else:
        # assume 24-hour format "H:MM"
        parts = t.split(":")
        return int(parts[0]) * 60 + int(parts[1])
    h, m = hm.split(":")
    h = int(h)
    m = int(m)
    if ampm == "AM":
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "Presidio",
    "Fisherman's Wharf",
    "Alamo Square",
    "Financial District",
    "Union Square",
    "Sunset District",
    "Embarcadero",
    "Golden Gate Park",
    "Chinatown",
    "Richmond District",
]

# Travel times (minutes), directional
travel_raw = {
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,

    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,

    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Richmond District"): 11,

    ("Financial District", "Presidio"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Richmond District"): 21,

    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Richmond District"): 20,

    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Richmond District"): 12,

    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Richmond District"): 21,

    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,

    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,

    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
}

# Build full travel dict with self travel = 0, and ensure all pairs queryable
travel = {a: {} for a in locations}
for a in locations:
    for b in locations:
        if a == b:
            travel[a][b] = 0
        else:
            travel[a][b] = travel_raw.get((a, b), None)

# Fill missing directions with a very large time to discourage impossible links
for a in locations:
    for b in locations:
        if travel[a][b] is None:
            travel[a][b] = 9999

# Participants: (name, location, available start, available end, min duration)
people = [
    ("Jeffrey", "Fisherman's Wharf", parse_time("10:15AM"), parse_time("1:00PM"), 90),
    ("Ronald", "Alamo Square", parse_time("7:45AM"), parse_time("2:45PM"), 120),
    ("Jason", "Financial District", parse_time("10:45AM"), parse_time("4:00PM"), 105),
    ("Melissa", "Union Square", parse_time("5:45PM"), parse_time("6:15PM"), 15),
    ("Elizabeth", "Sunset District", parse_time("2:45PM"), parse_time("5:30PM"), 105),
    ("Margaret", "Embarcadero", parse_time("1:15PM"), parse_time("7:00PM"), 90),
    ("George", "Golden Gate Park", parse_time("7:00PM"), parse_time("10:00PM"), 75),
    ("Richard", "Chinatown", parse_time("9:30AM"), parse_time("9:00PM"), 15),
    ("Laura", "Richmond District", parse_time("9:45AM"), parse_time("6:00PM"), 60),
]

n = len(people)
start_of_day = parse_time("9:00AM")
start_location = "Presidio"

# Z3 model
opt = Optimize()
opt.set(priority='lex')  # ensure lexicographic optimization

start_vars = []
end_exprs = []
meet_bools = []
first_bools = []

for i in range(n):
    name, loc, astart, aend, mindur = people[i]
    s = Int(f"start_{i}")
    start_vars.append(s)
    meet = Bool(f"meet_{i}")
    meet_bools.append(meet)
    first = Bool(f"first_{i}")
    first_bools.append(first)
    # Fixed-duration meeting
    end_exprs.append(s + mindur)

    # Bounds on start (keep broad; actual availability enforced when meeting)
    opt.add(s >= 0, s <= 24 * 60)

    # Availability window if meeting
    opt.add(Implies(meet, And(s >= astart, s + mindur <= aend)))

    # "First" implies we meet them
    opt.add(Implies(first, meet))

    # If first meeting, account for travel from starting location at 9:00
    opt.add(Implies(first, s >= start_of_day + travel[start_location][loc]))

# At most one "first"; exactly one if any meeting is scheduled
sum_meet = Sum([If(m, 1, 0) for m in meet_bools])
sum_first = Sum([If(f, 1, 0) for f in first_bools])
opt.add(sum_first <= 1)
opt.add(sum_first == If(sum_meet > 0, 1, 0))

# Travel feasibility and ordering
for i in range(n):
    name_i, loc_i, ai_start, ai_end, dur_i = people[i]
    for j in range(i + 1, n):
        name_j, loc_j, aj_start, aj_end, dur_j = people[j]
        dij = travel[loc_i][loc_j]
        dji = travel[loc_j][loc_i]
        # If both meetings happen, enforce a feasible order with travel time
        opt.add(Implies(And(meet_bools[i], meet_bools[j]),
                        Or(end_exprs[i] + dij <= start_vars[j],
                           end_exprs[j] + dji <= start_vars[i])))

    # If i is first, it precedes every other meeting with travel time
    for j in range(n):
        if j == i:
            continue
        dij = travel[loc_i][people[j][1]]
        opt.add(Implies(And(first_bools[i], meet_bools[j]),
                        end_exprs[i] + dij <= start_vars[j]))

# Objective: Maximize number of meetings; secondary: minimize latest end time
latest_end = Int("latest_end")
opt.add(latest_end >= 0, latest_end <= 24 * 60)
for i in range(n):
    opt.add(Implies(meet_bools[i], latest_end >= end_exprs[i]))

opt.maximize(sum_meet)
opt.minimize(latest_end)

# Solve
res = opt.check()
if res != sat:
    output = {"itinerary": []}
    print(json.dumps(output, indent=2))
else:
    model = opt.model()
    events = []
    for i in range(n):
        if is_true(model.evaluate(meet_bools[i], model_completion=True)):
            name, loc, astart, aend, mindur = people[i]
            s = model.evaluate(start_vars[i], model_completion=True).as_long()
            e = s + mindur
            events.append({
                "person": name,
                "location": loc,
                "start": s,
                "end": e
            })

    # Sort by start time
    events.sort(key=lambda x: x["start"])

    itinerary = []
    for ev in events:
        itinerary.append({
            "action": "meet",
            "location": ev["location"],
            "person": ev["person"],
            "start_time": minutes_to_str(ev["start"]),
            "end_time": minutes_to_str(ev["end"])
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))