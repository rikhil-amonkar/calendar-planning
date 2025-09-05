import json
from z3 import Optimize, Int, Bool, If, Or, And, Implies, Sum

def minutes_to_str(m):
    h = m // 60
    mn = m % 60
    return f"{h}:{mn:02d}"

# Locations
locations = [
    "The Castro",
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Richmond District",
    "Nob Hill",
    "Marina District",
    "Presidio",
    "Union Square",
    "Financial District",
]

# Travel times (in minutes) between locations
dist = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21,
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26,
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5,
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21,
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22,
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9,
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17,
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23,
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9,
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9,
    },
}

# Ensure diagonal zeros and symmetric fallbacks
for a in locations:
    if a not in dist:
        dist[a] = {}
    dist[a][a] = 0
    for b in locations:
        if a == b:
            dist[a][b] = 0
        else:
            if b not in dist[a]:
                # if missing, try reverse or default to a large number (shouldn't happen here)
                if a in dist and b in dist and a in dist[b]:
                    dist[a][b] = dist[b][a]
                else:
                    dist[a][b] = 9999

def travel(a, b):
    return dist[a][b]

# Day bounds
day_start = 9 * 60  # 9:00 -> 540
day_end = 21 * 60   # 21:00 -> 1260
start_location = "The Castro"

# Participants and constraints
people = [
    {"name": "Steven", "location": "North Beach", "window_start": 17*60+30, "window_end": 20*60+30, "min_duration": 15},
    {"name": "Sarah", "location": "Golden Gate Park", "window_start": 17*60, "window_end": 19*60+15, "min_duration": 75},
    {"name": "Brian", "location": "Embarcadero", "window_start": 14*60+15, "window_end": 16*60, "min_duration": 105},
    {"name": "Stephanie", "location": "Haight-Ashbury", "window_start": 10*60+15, "window_end": 12*60+15, "min_duration": 75},
    {"name": "Melissa", "location": "Richmond District", "window_start": 14*60, "window_end": 19*60+30, "min_duration": 30},
    {"name": "Nancy", "location": "Nob Hill", "window_start": 8*60+15, "window_end": 12*60+45, "min_duration": 90},
    {"name": "David", "location": "Marina District", "window_start": 11*60+15, "window_end": 13*60+15, "min_duration": 120},
    {"name": "James", "location": "Presidio", "window_start": 15*60, "window_end": 18*60+15, "min_duration": 120},
    {"name": "Elizabeth", "location": "Union Square", "window_start": 11*60+30, "window_end": 21*60, "min_duration": 60},
    {"name": "Robert", "location": "Financial District", "window_start": 13*60+15, "window_end": 15*60+15, "min_duration": 45},
]

def sanitize(s):
    return s.lower().replace(" ", "_").replace("-", "_")

# Build optimization model
opt = Optimize()
opt.set(priority='lex')

vars_map = {}
for p in people:
    sid = sanitize(p["name"])
    s = Int(f"start_{sid}")
    e = Int(f"end_{sid}")
    m = Bool(f"meet_{sid}")
    vars_map[p["name"]] = {"start": s, "end": e, "meet": m}
    # base bounds
    opt.add(s >= 0, e >= 0, e >= s, s <= 24*60, e <= 24*60)
    # meeting constraints guarded by 'meet'
    opt.add(Implies(m, And(
        s >= p["window_start"],
        s >= day_start,
        s >= day_start + travel(start_location, p["location"]),
        e <= p["window_end"],
        e <= day_end,
        (e - s) >= p["min_duration"]
    )))

# Non-overlap and travel-time feasibility between any two accepted meetings
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        vi = vars_map[pi["name"]]
        vj = vars_map[pj["name"]]
        tij = travel(pi["location"], pj["location"])
        tji = travel(pj["location"], pi["location"])
        opt.add(Implies(And(vi["meet"], vj["meet"]),
                        Or(vi["end"] + tij <= vj["start"],
                           vj["end"] + tji <= vi["start"])))


# Objectives: maximize number of meetings, then total minutes spent meeting
meet_count = Sum([If(vars_map[p["name"]]["meet"], 1, 0) for p in people])
total_minutes = Sum([If(vars_map[p["name"]]["meet"], vars_map[p["name"]]["end"] - vars_map[p["name"]]["start"], 0) for p in people])

opt.maximize(meet_count)
opt.maximize(total_minutes)

if opt.check() != None:
    model = opt.model()
    itinerary = []
    for p in people:
        v = vars_map[p["name"]]
        if model.evaluate(v["meet"], model_completion=True):
            start_min = model.evaluate(v["start"]).as_long()
            end_min = model.evaluate(v["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": minutes_to_str(start_min),
                "end_time": minutes_to_str(end_min),
            })
    # sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))