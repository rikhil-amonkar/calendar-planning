import json
from z3 import Optimize, Int, Bool, And, Or, Not, If, Sum, Implies, sat, is_true

# Helper functions
def parse_time(t):
    # t like '9:00AM' or '2:15PM'
    t = t.strip().upper()
    if t.endswith('AM'):
        ampm = 'AM'
        t = t[:-2]
    elif t.endswith('PM'):
        ampm = 'PM'
        t = t[:-2]
    else:
        raise ValueError("Time must end with AM or PM")
    h, m = map(int, t.split(':'))
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:  # PM
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Data
locations = [
    "Marina District",
    "Mission District",
    "Fisherman's Wharf",
    "Presidio",
    "Union Square",
    "Sunset District",
    "Financial District",
    "Haight-Ashbury",
    "Russian Hill",
]

# Directed travel times (minutes)
dist = {
    "Marina District": {
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Union Square": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Haight-Ashbury": 16,
        "Russian Hill": 8,
    },
    "Mission District": {
        "Marina District": 19,
        "Fisherman's Wharf": 22,
        "Presidio": 25,
        "Union Square": 15,
        "Sunset District": 24,
        "Financial District": 15,
        "Haight-Ashbury": 12,
        "Russian Hill": 15,
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Mission District": 22,
        "Presidio": 17,
        "Union Square": 13,
        "Sunset District": 27,
        "Financial District": 11,
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
    },
    "Presidio": {
        "Marina District": 11,
        "Mission District": 26,
        "Fisherman's Wharf": 19,
        "Union Square": 22,
        "Sunset District": 15,
        "Financial District": 23,
        "Haight-Ashbury": 15,
        "Russian Hill": 14,
    },
    "Union Square": {
        "Marina District": 18,
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Sunset District": 27,
        "Financial District": 9,
        "Haight-Ashbury": 18,
        "Russian Hill": 13,
    },
    "Sunset District": {
        "Marina District": 21,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Union Square": 30,
        "Financial District": 30,
        "Haight-Ashbury": 15,
        "Russian Hill": 24,
    },
    "Financial District": {
        "Marina District": 15,
        "Mission District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Union Square": 9,
        "Sunset District": 30,
        "Haight-Ashbury": 19,
        "Russian Hill": 11,
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Mission District": 11,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Union Square": 19,
        "Sunset District": 15,
        "Financial District": 21,
        "Russian Hill": 17,
    },
    "Russian Hill": {
        "Marina District": 7,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Union Square": 10,
        "Sunset District": 23,
        "Financial District": 11,
        "Haight-Ashbury": 17,
    },
}
# Add self distances as 0
for a in locations:
    dist.setdefault(a, {})
    dist[a][a] = 0

# People data: name, location, availability start, availability end, minimum duration
people = [
    {"name": "Karen", "location": "Mission District", "start": parse_time("2:15PM"), "end": parse_time("10:00PM"), "min_dur": 30},
    {"name": "Richard", "location": "Fisherman's Wharf", "start": parse_time("2:30PM"), "end": parse_time("5:30PM"), "min_dur": 30},
    {"name": "Robert", "location": "Presidio", "start": parse_time("9:45PM"), "end": parse_time("10:45PM"), "min_dur": 60},
    {"name": "Joseph", "location": "Union Square", "start": parse_time("11:45AM"), "end": parse_time("2:45PM"), "min_dur": 120},
    {"name": "Helen", "location": "Sunset District", "start": parse_time("2:45PM"), "end": parse_time("8:45PM"), "min_dur": 105},
    {"name": "Elizabeth", "location": "Financial District", "start": parse_time("10:00AM"), "end": parse_time("12:45PM"), "min_dur": 75},
    {"name": "Kimberly", "location": "Haight-Ashbury", "start": parse_time("2:15PM"), "end": parse_time("5:30PM"), "min_dur": 105},
    {"name": "Ashley", "location": "Russian Hill", "start": parse_time("11:30AM"), "end": parse_time("9:30PM"), "min_dur": 45},
]

start_location = "Marina District"
day_start = parse_time("9:00AM")

# Z3 setup
opt = Optimize()
opt.set(priority='lex')

vars_data = []
for p in people:
    s = Int(f"start_{p['name']}")
    e = Int(f"end_{p['name']}")
    m = Bool(f"meet_{p['name']}")
    vars_data.append({"p": p, "s": s, "e": e, "m": m})

    # Bounds
    opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)

    # Meeting constraints
    opt.add(If(m,
               And(s >= p["start"], e <= p["end"], e - s >= p["min_dur"]),
               And(e == s, s == p["start"])  # if not meeting, pin to window start (benign)
              ))

    # Reachability from initial location at day start
    opt.add(Implies(m, s >= day_start + dist[start_location][p["location"]]))

# Pairwise non-overlap with travel times
n = len(vars_data)
for i in range(n):
    for j in range(i + 1, n):
        pi = vars_data[i]["p"]
        pj = vars_data[j]["p"]
        si, ei, mi = vars_data[i]["s"], vars_data[i]["e"], vars_data[i]["m"]
        sj, ej, mj = vars_data[j]["s"], vars_data[j]["e"], vars_data[j]["m"]
        tij = dist[pi["location"]][pj["location"]]
        tji = dist[pj["location"]][pi["location"]]
        opt.add(Implies(And(mi, mj),
                        Or(ei + tij <= sj, ej + tji <= si)
                        ))

# Objectives
meet_count = Sum([If(v["m"], 1, 0) for v in vars_data])
total_meet_minutes = Sum([If(v["m"], v["e"] - v["s"], 0) for v in vars_data])
max_end = Int("max_end")
opt.add(max_end >= day_start)
for v in vars_data:
    opt.add(v["e"] <= max_end)

h1 = opt.maximize(meet_count)
h2 = opt.maximize(total_meet_minutes)
h3 = opt.minimize(max_end)

# Solve
res = opt.check()
if res != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit(0)

model = opt.model()

# Extract and sort itinerary
itinerary = []
for v in vars_data:
    if is_true(model.evaluate(v["m"], model_completion=True)):
        start_min = model.evaluate(v["s"]).as_long()
        end_min = model.evaluate(v["e"]).as_long()
        itinerary.append({
            "action": "meet",
            "location": v["p"]["location"],
            "person": v["p"]["name"],
            "start_time": fmt_time(start_min),
            "end_time": fmt_time(end_min),
        })

itinerary.sort(key=lambda x: (int(x["start_time"].split(':')[0]) * 60 + int(x["start_time"].split(':')[1])))

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))