import json
import re
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, Implies

def parse_time_12h(s):
    # Expect format like '7:00PM' or '8:30AM'
    m = re.match(r'^\s*(\d{1,2}):(\d{2})(AM|PM)\s*$', s, re.I)
    if not m:
        raise ValueError(f"Bad time: {s}")
    h = int(m.group(1))
    minute = int(m.group(2))
    ampm = m.group(3).upper()
    if h == 12:
        h = 0
    if ampm == 'PM':
        h += 12
    return h * 60 + minute

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (minutes)
times = {
    "The Castro": {
        "Marina District": 21, "Presidio": 20, "North Beach": 20, "Embarcadero": 22,
        "Haight-Ashbury": 6, "Golden Gate Park": 11, "Richmond District": 16,
        "Alamo Square": 8, "Financial District": 21, "Sunset District": 17
    },
    "Marina District": {
        "The Castro": 22, "Presidio": 10, "North Beach": 11, "Embarcadero": 14,
        "Haight-Ashbury": 16, "Golden Gate Park": 18, "Richmond District": 11,
        "Alamo Square": 15, "Financial District": 17, "Sunset District": 19
    },
    "Presidio": {
        "The Castro": 21, "Marina District": 11, "North Beach": 18, "Embarcadero": 20,
        "Haight-Ashbury": 15, "Golden Gate Park": 12, "Richmond District": 7,
        "Alamo Square": 19, "Financial District": 23, "Sunset District": 15
    },
    "North Beach": {
        "The Castro": 23, "Marina District": 9, "Presidio": 17, "Embarcadero": 6,
        "Haight-Ashbury": 18, "Golden Gate Park": 22, "Richmond District": 18,
        "Alamo Square": 16, "Financial District": 8, "Sunset District": 27
    },
    "Embarcadero": {
        "The Castro": 25, "Marina District": 12, "Presidio": 20, "North Beach": 5,
        "Haight-Ashbury": 21, "Golden Gate Park": 25, "Richmond District": 21,
        "Alamo Square": 19, "Financial District": 5, "Sunset District": 30
    },
    "Haight-Ashbury": {
        "The Castro": 6, "Marina District": 17, "Presidio": 15, "North Beach": 19,
        "Embarcadero": 20, "Golden Gate Park": 7, "Richmond District": 10,
        "Alamo Square": 5, "Financial District": 21, "Sunset District": 15
    },
    "Golden Gate Park": {
        "The Castro": 13, "Marina District": 16, "Presidio": 11, "North Beach": 23,
        "Embarcadero": 25, "Haight-Ashbury": 7, "Richmond District": 7,
        "Alamo Square": 9, "Financial District": 26, "Sunset District": 10
    },
    "Richmond District": {
        "The Castro": 16, "Marina District": 9, "Presidio": 7, "North Beach": 17,
        "Embarcadero": 19, "Haight-Ashbury": 10, "Golden Gate Park": 9,
        "Alamo Square": 13, "Financial District": 22, "Sunset District": 11
    },
    "Alamo Square": {
        "The Castro": 8, "Marina District": 15, "Presidio": 17, "North Beach": 15,
        "Embarcadero": 16, "Haight-Ashbury": 5, "Golden Gate Park": 9,
        "Richmond District": 11, "Financial District": 17, "Sunset District": 16
    },
    "Financial District": {
        "The Castro": 20, "Marina District": 15, "Presidio": 22, "North Beach": 7,
        "Embarcadero": 4, "Haight-Ashbury": 19, "Golden Gate Park": 23,
        "Richmond District": 21, "Alamo Square": 17, "Sunset District": 30
    },
    "Sunset District": {
        "The Castro": 17, "Marina District": 21, "Presidio": 16, "North Beach": 28,
        "Embarcadero": 30, "Haight-Ashbury": 15, "Golden Gate Park": 11,
        "Richmond District": 12, "Alamo Square": 17, "Financial District": 30
    }
}

# People and constraints
people = [
    {"name": "Elizabeth", "location": "Marina District", "start": parse_time_12h("7:00PM"), "end": parse_time_12h("8:45PM"), "min_dur": 105},
    {"name": "Joshua", "location": "Presidio", "start": parse_time_12h("8:30AM"), "end": parse_time_12h("1:15PM"), "min_dur": 105},
    {"name": "Timothy", "location": "North Beach", "start": parse_time_12h("7:45PM"), "end": parse_time_12h("10:00PM"), "min_dur": 90},
    {"name": "David", "location": "Embarcadero", "start": parse_time_12h("10:45AM"), "end": parse_time_12h("12:30PM"), "min_dur": 30},
    {"name": "Kimberly", "location": "Haight-Ashbury", "start": parse_time_12h("4:45PM"), "end": parse_time_12h("9:30PM"), "min_dur": 75},
    {"name": "Lisa", "location": "Golden Gate Park", "start": parse_time_12h("5:30PM"), "end": parse_time_12h("9:45PM"), "min_dur": 45},
    {"name": "Ronald", "location": "Richmond District", "start": parse_time_12h("8:00AM"), "end": parse_time_12h("9:30AM"), "min_dur": 90},
    {"name": "Stephanie", "location": "Alamo Square", "start": parse_time_12h("3:30PM"), "end": parse_time_12h("4:30PM"), "min_dur": 30},
    {"name": "Helen", "location": "Financial District", "start": parse_time_12h("5:30PM"), "end": parse_time_12h("6:30PM"), "min_dur": 45},
    {"name": "Laura", "location": "Sunset District", "start": parse_time_12h("5:45PM"), "end": parse_time_12h("9:15PM"), "min_dur": 90},
]

start_location = "The Castro"
arrival_time = parse_time_12h("9:00AM")

opt = Optimize()
opt.set("opt.priority", "lex")

# Z3 variables
starts = {}
ends = {}
meets = {}

# Bounds for day (0..1440)
DAY_MIN = 0
DAY_MAX = 24 * 60

for p in people:
    name = p["name"]
    starts[name] = Int(f"start_{name}")
    ends[name] = Int(f"end_{name}")
    meets[name] = Bool(f"meet_{name}")

    # Variable bounds
    opt.add(starts[name] >= DAY_MIN, starts[name] <= DAY_MAX)
    opt.add(ends[name] >= DAY_MIN, ends[name] <= DAY_MAX)

    # Meeting window and duration constraints
    ws, we, req = p["start"], p["end"], p["min_dur"]

    opt.add(
        Or(
            And(
                meets[name],
                starts[name] >= ws,
                ends[name] <= we,
                ends[name] >= starts[name],
                ends[name] - starts[name] >= req
            ),
            And(
                Not(meets[name]),
                starts[name] == ws,  # fix unused vars to reduce search space
                ends[name] == ws
            )
        )
    )

    # Reachability from starting point (if we meet them)
    # You must be able to arrive from The Castro at 9:00 before meeting start
    travel_from_start = times[start_location][p["location"]]
    opt.add(Implies(meets[name], starts[name] >= arrival_time + travel_from_start))

# Disjunctive scheduling constraints with travel times between any two met meetings
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        ni = pi["name"]
        nj = pj["name"]
        t_ij = times[pi["location"]][pj["location"]]
        t_ji = times[pj["location"]][pi["location"]]
        opt.add(
            Implies(
                And(meets[ni], meets[nj]),
                Or(
                    ends[ni] + t_ij <= starts[nj],
                    ends[nj] + t_ji <= starts[ni]
                )
            )
        )

# Objectives: maximize number of meetings, then total meeting minutes
num_met = Sum([If(meets[p["name"]], 1, 0) for p in people])
total_minutes = Sum([If(meets[p["name"]], ends[p["name"]] - starts[p["name"]], 0) for p in people])

opt.maximize(num_met)
opt.maximize(total_minutes)

if opt.check() != None:
    model = opt.model()
    itinerary = []
    for p in people:
        name = p["name"]
        if model.evaluate(meets[name]).is_true():
            s = model.evaluate(starts[name]).as_long()
            e = model.evaluate(ends[name]).as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e)
            })
    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))
else:
    print(json.dumps({"itinerary": []}))