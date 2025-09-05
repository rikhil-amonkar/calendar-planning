from z3 import *
import json

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Constants (minutes since midnight)
BAYVIEW_ARRIVAL = 9 * 60  # 9:00
DAY_END = 13 * 60         # 13:00

# Locations
US = 0  # Union Square
PR = 1  # Presidio

# Travel times (directed, in minutes)
# Bayview to locations
BV_to = {
    US: 17,
    PR: 31
}

# Between locations (directed)
between = {
    (US, PR): 24,
    (PR, US): 22,
    (US, US): 0,
    (PR, PR): 0
}

# Friends' availability and requirements
friends = [
    {
        "name": "Richard",
        "location": US,
        "location_name": "Union Square",
        "avail_start": 8 * 60 + 45,  # 8:45
        "avail_end": 13 * 60,        # 13:00
        "required_min": 120
    },
    {
        "name": "Charles",
        "location": PR,
        "location_name": "Presidio",
        "avail_start": 9 * 60 + 45,  # 9:45
        "avail_end": 13 * 60,        # 13:00
        "required_min": 120
    }
]

# Helper to create z3 expression for travel from Bayview to loc
def travel_from_bayview_expr(loc):
    return If(loc == US, IntVal(BV_to[US]), IntVal(BV_to[PR]))

# Helper to create z3 expression for travel between two z3 location vars
def travel_between_expr(loc_from, loc_to):
    return If(And(loc_from == US, loc_to == PR), IntVal(between[(US, PR)]),
           If(And(loc_from == PR, loc_to == US), IntVal(between[(PR, US)]),
              If(loc_from == loc_to, IntVal(0), IntVal(0))))

# Overlap between [s, e] and [a, b] as z3 Int expression
def overlap_expr(s, e, a, b):
    min_end = If(e <= b, e, IntVal(b))
    max_start = If(s >= a, s, IntVal(a))
    diff = min_end - max_start
    return If(diff > 0, diff, IntVal(0))

# Build optimization model
opt = Optimize()
opt.set(priority='lex')

# Number of time segments to consider
N = 3

loc = [Int(f"loc_{i}") for i in range(N)]
s = [Int(f"s_{i}") for i in range(N)]
e = [Int(f"e_{i}") for i in range(N)]

# Domain constraints
for i in range(N):
    opt.add(Or(loc[i] == US, loc[i] == PR))
    opt.add(s[i] >= 0, e[i] >= s[i], e[i] <= DAY_END, s[i] <= DAY_END)

# Timing constraints with travel
# First segment: must start no earlier than available after traveling from Bayview
opt.add(s[0] >= BAYVIEW_ARRIVAL + travel_from_bayview_expr(loc[0]))

# Subsequent segments: respect travel times between chosen locations
for i in range(1, N):
    opt.add(s[i] >= e[i-1] + travel_between_expr(loc[i-1], loc[i]))

# Compute meeting overlaps per friend
sum_meet = {}
sat = {}
met = {}
total_meeting_time = IntVal(0)

for fr in friends:
    overlaps = []
    for i in range(N):
        ov = If(loc[i] == fr["location"],
                overlap_expr(s[i], e[i], fr["avail_start"], fr["avail_end"]),
                IntVal(0))
        overlaps.append(ov)
    total = Sum(overlaps)
    sum_meet[fr["name"]] = total

    # Binary indicators for satisfaction of minimum and whether met at all
    sat_var = Int(f"sat_{fr['name']}")
    met_var = Int(f"met_{fr['name']}")
    opt.add(And(sat_var >= 0, sat_var <= 1))
    opt.add(And(met_var >= 0, met_var <= 1))

    # sat_var == 1 -> total >= required_min; sat_var == 0 -> total <= required_min - 1
    opt.add(Implies(sat_var == 1, total >= fr["required_min"]))
    opt.add(Implies(sat_var == 0, total <= fr["required_min"] - 1))

    # met_var == 1 -> total >= 1; met_var == 0 -> total == 0
    opt.add(Implies(met_var == 1, total >= 1))
    opt.add(Implies(met_var == 0, total == 0))

    sat[fr["name"]] = sat_var
    met[fr["name"]] = met_var
    total_meeting_time = total_meeting_time + total

# Objectives:
# 1) Maximize number of friends who meet their minimum requirement
opt.maximize(Sum([sat[fr["name"]] for fr in friends]))
# 2) Maximize number of distinct friends met at all
opt.maximize(Sum([met[fr["name"]] for fr in friends]))
# 3) Maximize total meeting time
opt.maximize(total_meeting_time)

# Solve
if opt.check() != sat_result := sat:
    pass  # placeholder to avoid linter warnings

res = opt.check()
if res != sat:
    # Fallback to empty itinerary if something goes wrong
    print(json.dumps({"itinerary": []}))
    exit(0)

model = opt.model()

# Extract segments and build itinerary of meeting intervals
entries = []

# Helper to get model int value
def mval(x):
    return model[x].as_long()

seg_vals = []
for i in range(N):
    seg_vals.append({
        "i": i,
        "loc": mval(loc[i]),
        "s": mval(s[i]),
        "e": mval(e[i])
    })

for seg in seg_vals:
    for fr in friends:
        if seg["loc"] == fr["location"]:
            start_meet = max(seg["s"], fr["avail_start"])
            end_meet = min(seg["e"], fr["avail_end"])
            if end_meet > start_meet:
                entries.append({
                    "action": "meet",
                    "location": fr["location_name"],
                    "person": fr["name"],
                    "start_time": minutes_to_str(start_meet),
                    "end_time": minutes_to_str(end_meet),
                    "_start_min": start_meet  # for sorting
                })

# Sort by start time
entries.sort(key=lambda x: x["_start_min"])
# Remove helper key
for eobj in entries:
    eobj.pop("_start_min", None)

output = {
    "itinerary": entries
}

print(json.dumps(output, ensure_ascii=False))