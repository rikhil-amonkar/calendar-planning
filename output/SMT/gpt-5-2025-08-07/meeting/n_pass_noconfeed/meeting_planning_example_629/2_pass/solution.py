# This script computes an optimal meeting itinerary using Z3 SMT solver.
# It maximizes the number of friends met (subject to travel and availability),
# and, as a tiebreaker, maximizes total meeting time.

import json
from z3 import Int, Bool, Optimize, And, Or, Implies, If, Sum, sat, is_true

# Time helpers
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Russian Hill",
    "Presidio",
    "Chinatown",
    "Pacific Heights",
    "Richmond District",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Bayview"
]

# Travel times in minutes between locations
t = {loc: {} for loc in locations}
# Initialize same-location travel to 0
for loc in locations:
    t[loc][loc] = 0

# Fill provided travel times
# From Russian Hill
t["Russian Hill"]["Presidio"] = 14
t["Russian Hill"]["Chinatown"] = 9
t["Russian Hill"]["Pacific Heights"] = 7
t["Russian Hill"]["Richmond District"] = 14
t["Russian Hill"]["Fisherman's Wharf"] = 7
t["Russian Hill"]["Golden Gate Park"] = 21
t["Russian Hill"]["Bayview"] = 23
# From Presidio
t["Presidio"]["Russian Hill"] = 14
t["Presidio"]["Chinatown"] = 21
t["Presidio"]["Pacific Heights"] = 11
t["Presidio"]["Richmond District"] = 7
t["Presidio"]["Fisherman's Wharf"] = 19
t["Presidio"]["Golden Gate Park"] = 12
t["Presidio"]["Bayview"] = 31
# From Chinatown
t["Chinatown"]["Russian Hill"] = 7
t["Chinatown"]["Presidio"] = 19
t["Chinatown"]["Pacific Heights"] = 10
t["Chinatown"]["Richmond District"] = 20
t["Chinatown"]["Fisherman's Wharf"] = 8
t["Chinatown"]["Golden Gate Park"] = 23
t["Chinatown"]["Bayview"] = 22
# From Pacific Heights
t["Pacific Heights"]["Russian Hill"] = 7
t["Pacific Heights"]["Presidio"] = 11
t["Pacific Heights"]["Chinatown"] = 11
t["Pacific Heights"]["Richmond District"] = 12
t["Pacific Heights"]["Fisherman's Wharf"] = 13
t["Pacific Heights"]["Golden Gate Park"] = 15
t["Pacific Heights"]["Bayview"] = 22
# From Richmond District
t["Richmond District"]["Russian Hill"] = 13
t["Richmond District"]["Presidio"] = 7
t["Richmond District"]["Chinatown"] = 20
t["Richmond District"]["Pacific Heights"] = 10
t["Richmond District"]["Fisherman's Wharf"] = 18
t["Richmond District"]["Golden Gate Park"] = 9
t["Richmond District"]["Bayview"] = 26
# From Fisherman's Wharf
t["Fisherman's Wharf"]["Russian Hill"] = 7
t["Fisherman's Wharf"]["Presidio"] = 17
t["Fisherman's Wharf"]["Chinatown"] = 12
t["Fisherman's Wharf"]["Pacific Heights"] = 12
t["Fisherman's Wharf"]["Richmond District"] = 18
t["Fisherman's Wharf"]["Golden Gate Park"] = 25
t["Fisherman's Wharf"]["Bayview"] = 26
# From Golden Gate Park
t["Golden Gate Park"]["Russian Hill"] = 19
t["Golden Gate Park"]["Presidio"] = 11
t["Golden Gate Park"]["Chinatown"] = 23
t["Golden Gate Park"]["Pacific Heights"] = 16
t["Golden Gate Park"]["Richmond District"] = 7
t["Golden Gate Park"]["Fisherman's Wharf"] = 24
t["Golden Gate Park"]["Bayview"] = 23
# From Bayview
t["Bayview"]["Russian Hill"] = 23
t["Bayview"]["Presidio"] = 31
t["Bayview"]["Chinatown"] = 18
t["Bayview"]["Pacific Heights"] = 23
t["Bayview"]["Richmond District"] = 25
t["Bayview"]["Fisherman's Wharf"] = 25
t["Bayview"]["Golden Gate Park"] = 22

# People data: location, availability window, and minimum meeting duration
# Times in minutes since midnight
people = [
    {
        "name": "Matthew",
        "location": "Presidio",
        "avail_start": to_minutes(11, 0),
        "avail_end": to_minutes(21, 0),
        "min_duration": 90
    },
    {
        "name": "Margaret",
        "location": "Chinatown",
        "avail_start": to_minutes(9, 15),
        "avail_end": to_minutes(18, 45),
        "min_duration": 90
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "avail_start": to_minutes(14, 15),
        "avail_end": to_minutes(17, 0),
        "min_duration": 15
    },
    {
        "name": "Helen",
        "location": "Richmond District",
        "avail_start": to_minutes(19, 45),
        "avail_end": to_minutes(22, 0),
        "min_duration": 60
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "avail_start": to_minutes(21, 15),
        "avail_end": to_minutes(22, 15),
        "min_duration": 60
    },
    {
        "name": "Kimberly",
        "location": "Golden Gate Park",
        "avail_start": to_minutes(13, 0),
        "avail_end": to_minutes(16, 30),
        "min_duration": 120
    },
    {
        "name": "Kenneth",
        "location": "Bayview",
        "avail_start": to_minutes(14, 30),
        "avail_end": to_minutes(18, 0),
        "min_duration": 60
    },
]

# Day settings
start_location = "Russian Hill"
day_start = to_minutes(9, 0)
# Slightly beyond last possible meeting end for domain safety
day_end = to_minutes(23, 59)

# Setup Z3 Optimize
opt = Optimize()

# Variables per person
vars_map = {}
for p in people:
    name = p["name"]
    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    meet = Bool(f"meet_{name}")
    vars_map[name] = {"s": s, "e": e, "meet": meet}

    # Time bounds within day
    opt.add(s >= day_start, s <= day_end)
    opt.add(e >= day_start, e <= day_end)
    # Respect availability window when meeting status considered
    opt.add(s >= p["avail_start"])
    opt.add(e <= p["avail_end"])
    opt.add(e >= s)

    # Meeting duration constraints controlled by meet boolean
    min_dur = p["min_duration"]
    max_dur = p["avail_end"] - p["avail_start"]
    # If meeting, ensure minimum duration; if not, duration 0
    opt.add(e - s >= If(meet, min_dur, 0))
    opt.add(e - s <= If(meet, max_dur, 0))

    # Start-of-day travel feasibility: if meeting, can't start before arrival from start location
    opt.add(Implies(meet, s >= day_start + t[start_location][p["location"]]))

# Pairwise disjunctive scheduling with travel times
n = len(people)
for i in range(n):
    for j in range(i + 1, n):
        pi = people[i]
        pj = people[j]
        vi = vars_map[pi["name"]]
        vj = vars_map[pj["name"]]
        travel_ij = t[pi["location"]][pj["location"]]
        travel_ji = t[pj["location"]][pi["location"]]
        # If both meetings happen, enforce that one finishes and travel before the other starts
        opt.add(Implies(And(vi["meet"], vj["meet"]),
                        Or(vi["e"] + travel_ij <= vj["s"],
                           vj["e"] + travel_ji <= vi["s"])))


# Objectives:
# 1) Maximize number of meetings
meet_count = Sum([If(vars_map[p["name"]]["meet"], 1, 0) for p in people])
opt.maximize(meet_count)
# 2) Maximize total meeting minutes as tie-breaker
total_minutes = Sum([vars_map[p["name"]]["e"] - vars_map[p["name"]]["s"] for p in people])
opt.maximize(total_minutes)

# Optional 3rd objective placeholder (not used)
latest_end = Int("latest_end")
opt.add(latest_end == Sum([If(vars_map[p["name"]]["meet"], vars_map[p["name"]]["e"], day_start) for p in people]))

# Solve
if opt.check() == sat:
    m = opt.model()
    # Build itinerary
    itinerary = []
    for p in people:
        name = p["name"]
        v = vars_map[name]
        if is_true(m.eval(v["meet"], model_completion=True)):
            s_val = m.eval(v["s"], model_completion=True).as_long()
            e_val = m.eval(v["e"], model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": fmt_time(s_val),
                "end_time": fmt_time(e_val),
                "_start_minutes": s_val  # helper for sorting
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["_start_minutes"])
    # Remove helper key
    for item in itinerary:
        item.pop("_start_minutes", None)
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, ensure_ascii=False, indent=2))