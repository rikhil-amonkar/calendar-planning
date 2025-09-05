import json
from z3 import Int, Bool, If, And, Or, Sum, Optimize, Implies, Not, sat

# Helper functions
def t(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) as a directed graph
travel = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,

    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,

    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,

    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Golden Gate Park"): 15,

    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,

    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,

    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,

    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Golden Gate Park"): 11,

    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
}

def get_travel(a, b):
    return travel[(a, b)]

# Input parameters as variables
arrival_location = "Haight-Ashbury"
arrival_time = t(9, 0)  # 9:00

friends = [
    {"name": "Elizabeth", "location": "Mission District",       "avail_start": t(10, 30), "avail_end": t(20, 0),  "min_dur": 90},
    {"name": "David",     "location": "Union Square",           "avail_start": t(15, 15), "avail_end": t(19, 0),  "min_dur": 45},
    {"name": "Sandra",    "location": "Pacific Heights",        "avail_start": t(7, 0),   "avail_end": t(20, 0),  "min_dur": 120},
    {"name": "Thomas",    "location": "Bayview",                "avail_start": t(19, 30), "avail_end": t(20, 30), "min_dur": 30},
    {"name": "Robert",    "location": "Fisherman's Wharf",      "avail_start": t(10, 0),  "avail_end": t(15, 0),  "min_dur": 15},
    {"name": "Kenneth",   "location": "Marina District",        "avail_start": t(10, 45), "avail_end": t(13, 0),  "min_dur": 45},
    {"name": "Melissa",   "location": "Richmond District",      "avail_start": t(18, 15), "avail_end": t(20, 0),  "min_dur": 15},
    {"name": "Kimberly",  "location": "Sunset District",        "avail_start": t(10, 15), "avail_end": t(18, 15), "min_dur": 105},
    {"name": "Amanda",    "location": "Golden Gate Park",       "avail_start": t(7, 45),  "avail_end": t(18, 45), "min_dur": 15},
]

# Z3 variables
opt = Optimize()
N = len(friends)

meet = {}
start = {}
dur = {}
end = {}

for f in friends:
    name = f["name"]
    meet[name] = Bool(f"meet_{name}")
    start[name] = Int(f"start_{name}")
    dur[name] = Int(f"dur_{name}")
    end[name] = Int(f"end_{name}")

    # Basic definitions and bounds
    opt.add(end[name] == start[name] + dur[name])
    opt.add(start[name] >= 0, dur[name] >= 0, end[name] >= 0)

    # Availability and minimum duration when meeting; otherwise no duration
    opt.add(
        If(
            meet[name],
            And(
                start[name] >= f["avail_start"],
                end[name] <= f["avail_end"],
                dur[name] >= f["min_dur"]
            ),
            And(dur[name] == 0, start[name] == 0, end[name] == 0)
        )
    )

    # Must be reachable from arrival
    opt.add(
        Implies(
            meet[name],
            start[name] >= arrival_time + get_travel(arrival_location, f["location"])
        )
    )

# Pairwise non-overlap with travel times using order variables
order = {}  # (i,j) for i<j
for i in range(N):
    for j in range(i + 1, N):
        fi = friends[i]
        fj = friends[j]
        key = (fi["name"], fj["name"])
        order[key] = Bool(f"order_{fi['name']}_before_{fj['name']}")

        # If both meetings happen and fi is before fj
        opt.add(
            Implies(
                And(meet[fi["name"]], meet[fj["name"]], order[key]),
                start[fj["name"]] >= end[fi["name"]] + get_travel(fi["location"], fj["location"])
            )
        )
        # If both meetings happen and fj is before fi
        opt.add(
            Implies(
                And(meet[fi["name"]], meet[fj["name"]], Not(order[key])),
                start[fi["name"]] >= end[fj["name"]] + get_travel(fj["location"], fi["location"])
            )
        )

# Objective: maximize number of friends met
total_met = Sum([If(meet[f["name"]], 1, 0) for f in friends])
opt.maximize(total_met)

# Solve
result = {}
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for f in friends:
        name = f["name"]
        if m.evaluate(meet[name]).is_true():
            s = m.evaluate(start[name]).as_long()
            e = m.evaluate(end[name]).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e),
            })
    # Sort by start_time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    result["itinerary"] = itinerary
else:
    result["itinerary"] = []

print(json.dumps(result, ensure_ascii=False))