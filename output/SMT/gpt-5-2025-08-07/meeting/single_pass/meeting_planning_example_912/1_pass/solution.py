# Solve the SF friend-meeting schedule with Z3 to maximize number of friends met
# Subject to travel times and time windows.

from z3 import *
import json

# Base time in minutes from midnight for 09:00
BASE = 9 * 60

def tmin(hh_mm):
    hh, mm = map(int, hh_mm.split(":"))
    return hh * 60 + mm

def fmt_time(minutes_from_base):
    tot = BASE + minutes_from_base
    hh = tot // 60
    mm = tot % 60
    return f"{hh:02d}:{mm:02d}"

# Locations
US = "Union Square"
locs = [
    "Union Square","Presidio","Alamo Square","Marina District","Financial District",
    "Nob Hill","Sunset District","Chinatown","Russian Hill","North Beach","Haight-Ashbury"
]

# Directed travel times (minutes), as provided
t = {L:{} for L in locs}

# Fill travel times
t["Union Square"].update({
    "Presidio":24, "Alamo Square":15, "Marina District":18, "Financial District":9,
    "Nob Hill":9, "Sunset District":27, "Chinatown":7, "Russian Hill":13,
    "North Beach":10, "Haight-Ashbury":18
})
t["Presidio"].update({
    "Union Square":22, "Alamo Square":19, "Marina District":11, "Financial District":23,
    "Nob Hill":18, "Sunset District":15, "Chinatown":21, "Russian Hill":14,
    "North Beach":18, "Haight-Ashbury":15
})
t["Alamo Square"].update({
    "Union Square":14, "Presidio":17, "Marina District":15, "Financial District":17,
    "Nob Hill":11, "Sunset District":16, "Chinatown":15, "Russian Hill":13,
    "North Beach":15, "Haight-Ashbury":5
})
t["Marina District"].update({
    "Union Square":16, "Presidio":10, "Alamo Square":15, "Financial District":17,
    "Nob Hill":12, "Sunset District":19, "Chinatown":15, "Russian Hill":8,
    "North Beach":11, "Haight-Ashbury":16
})
t["Financial District"].update({
    "Union Square":9, "Presidio":22, "Alamo Square":17, "Marina District":15,
    "Nob Hill":8, "Sunset District":30, "Chinatown":5, "Russian Hill":11,
    "North Beach":7, "Haight-Ashbury":19
})
t["Nob Hill"].update({
    "Union Square":7, "Presidio":17, "Alamo Square":11, "Marina District":11,
    "Financial District":9, "Sunset District":24, "Chinatown":6, "Russian Hill":5,
    "North Beach":8, "Haight-Ashbury":13
})
t["Sunset District"].update({
    "Union Square":30, "Presidio":16, "Alamo Square":17, "Marina District":21,
    "Financial District":30, "Nob Hill":27, "Chinatown":30, "Russian Hill":24,
    "North Beach":28, "Haight-Ashbury":15
})
t["Chinatown"].update({
    "Union Square":7, "Presidio":19, "Alamo Square":17, "Marina District":12,
    "Financial District":5, "Nob Hill":9, "Sunset District":29, "Russian Hill":7,
    "North Beach":3, "Haight-Ashbury":19
})
t["Russian Hill"].update({
    "Union Square":10, "Presidio":14, "Alamo Square":15, "Marina District":7,
    "Financial District":11, "Nob Hill":5, "Sunset District":23, "Chinatown":9,
    "North Beach":5, "Haight-Ashbury":17
})
t["North Beach"].update({
    "Union Square":7, "Presidio":17, "Alamo Square":16, "Marina District":9,
    "Financial District":8, "Nob Hill":7, "Sunset District":27, "Chinatown":6,
    "Russian Hill":4, "Haight-Ashbury":18
})
t["Haight-Ashbury"].update({
    "Union Square":19, "Presidio":15, "Alamo Square":5, "Marina District":17,
    "Financial District":21, "Nob Hill":15, "Sunset District":15, "Chinatown":19,
    "Russian Hill":17, "North Beach":19
})

# Friend availability and minimum meeting durations
friends = [
    # name, location, available_start, available_end, min_meet
    ("Kimberly", "Presidio",          "15:30", "16:00", 15),
    ("Elizabeth","Alamo Square",      "19:15", "20:15", 15),
    ("Joshua",   "Marina District",   "10:30", "14:15", 45),
    ("Sandra",   "Financial District","19:30", "20:15", 45),
    ("Kenneth",  "Nob Hill",          "12:45", "21:45", 30),
    ("Betty",    "Sunset District",   "14:00", "19:00", 60),
    ("Deborah",  "Chinatown",         "17:15", "20:30", 15),
    ("Barbara",  "Russian Hill",      "17:30", "21:15", 120),
    ("Steven",   "North Beach",       "17:45", "20:45", 90),
    ("Daniel",   "Haight-Ashbury",    "18:30", "18:45", 15),
]

# Convert to numeric windows relative to BASE
people = []
for name, loc, s, e, d in friends:
    ws = tmin(s) - BASE
    we = tmin(e) - BASE
    people.append({
        "name": name,
        "loc": loc,
        "ws": ws,
        "we": we,
        "dur": d
    })

# Horizon: a bit beyond the last end time relative to BASE
H = max(p["we"] for p in people) + 60

opt = Optimize()

# Decision variables
meet = {}
start = {}

for p in people:
    meet[p["name"]] = Bool(f"meet_{p['name']}")
    start[p["name"]] = Int(f"start_{p['name']}")
    # Bounds and window constraints
    opt.add(And(start[p["name"]] >= 0, start[p["name"]] <= H))
    # If meeting, must be within availability window
    opt.add(Implies(meet[p["name"]],
                    And(start[p["name"]] >= p["ws"],
                        start[p["name"]] + p["dur"] <= p["we"])))
    # If meeting, must be reachable from origin at 09:00
    opt.add(Implies(meet[p["name"]], start[p["name"]] >= t[US][p["loc"]]))

# Pairwise disjunctive no-overlap constraints with travel times
order = {}
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]; pj = people[j]
        key = (pi["name"], pj["name"])
        order[key] = Bool(f"order_{pi['name']}_before_{pj['name']}")
        ti_j = t[pi["loc"]][pj["loc"]]
        tj_i = t[pj["loc"]][pi["loc"]]
        si = start[pi["name"]]
        sj = start[pj["name"]]
        di = pi["dur"]
        dj = pj["dur"]
        mi = meet[pi["name"]]
        mj = meet[pj["name"]]
        # If both are met and i before j
        opt.add(Implies(And(mi, mj, order[key]), sj >= si + di + ti_j))
        # If both are met and j before i
        opt.add(Implies(And(mi, mj, Not(order[key])), si >= sj + dj + tj_i))

# Objective: maximize number of friends met; tie-breaker minimize total idle/makespan
total_met = Sum([If(meet[p["name"]], 1, 0) for p in people])
opt.maximize(total_met)

# Optional tie-breakers: minimize latest end time to encourage earlier schedules
latest_end = Int("latest_end")
opt.add(latest_end >= 0)
for p in people:
    opt.add(Implies(meet[p["name"]], latest_end >= start[p["name"]] + p["dur"]))
opt.minimize(latest_end)

res = opt.check()
if res != sat and res != unknown:
    raise RuntimeError("No feasible schedule found")

m = opt.model()

# Build itinerary from model
itins = []
for p in people:
    if m.evaluate(meet[p["name"]], model_completion=True):
        st = m.evaluate(start[p["name"]]).as_long()
        et = st + p["dur"]
        itins.append({
            "action": "meet",
            "person": p["name"],
            "start_time": fmt_time(st),
            "end_time": fmt_time(et)
        })

# Sort by start time
itins.sort(key=lambda x: x["start_time"])

print(json.dumps({"itinerary": itins}, ensure_ascii=False))