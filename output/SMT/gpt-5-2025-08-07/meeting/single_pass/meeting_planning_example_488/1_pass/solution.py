# Solve the SF day meetup scheduling problem with Z3 Optimize
# Objective: maximize number of friends met while respecting travel times and availability windows.

from z3 import *
import json

# Helpers
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return 60*h + m

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Data
start_location = "Pacific Heights"
day_start = to_minutes("09:00")  # arrive at Pacific Heights at 09:00

people = [
    # name, location, start_time, end_time, min_duration
    ("Ronald",   "Nob Hill",        "10:00", "17:00", 105),
    ("Sarah",    "Russian Hill",    "07:15", "09:30",  45),
    ("Helen",    "The Castro",      "13:30", "17:00", 120),
    ("Joshua",   "Sunset District", "14:15", "19:30",  90),
    ("Margaret", "Haight-Ashbury",  "10:15", "22:00",  60),
]

# Directed travel times (minutes)
T = {}
def set_t(a,b,t):
    T[(a,b)] = t

# Given travel times
set_t("Pacific Heights","Nob Hill",8)
set_t("Pacific Heights","Russian Hill",7)
set_t("Pacific Heights","The Castro",16)
set_t("Pacific Heights","Sunset District",21)
set_t("Pacific Heights","Haight-Ashbury",11)

set_t("Nob Hill","Pacific Heights",8)
set_t("Nob Hill","Russian Hill",5)
set_t("Nob Hill","The Castro",17)
set_t("Nob Hill","Sunset District",25)
set_t("Nob Hill","Haight-Ashbury",13)

set_t("Russian Hill","Pacific Heights",7)
set_t("Russian Hill","Nob Hill",5)
set_t("Russian Hill","The Castro",21)
set_t("Russian Hill","Sunset District",23)
set_t("Russian Hill","Haight-Ashbury",17)

set_t("The Castro","Pacific Heights",16)
set_t("The Castro","Nob Hill",16)
set_t("The Castro","Russian Hill",18)
set_t("The Castro","Sunset District",17)
set_t("The Castro","Haight-Ashbury",6)

set_t("Sunset District","Pacific Heights",21)
set_t("Sunset District","Nob Hill",27)
set_t("Sunset District","Russian Hill",24)
set_t("Sunset District","The Castro",17)
set_t("Sunset District","Haight-Ashbury",15)

set_t("Haight-Ashbury","Pacific Heights",12)
set_t("Haight-Ashbury","Nob Hill",15)
set_t("Haight-Ashbury","Russian Hill",17)
set_t("Haight-Ashbury","The Castro",6)
set_t("Haight-Ashbury","Sunset District",15)

# Build model
opt = Optimize()

# Variables
meet = {}
start = {}
end = {}

# Precompute availability windows relative to day_start (09:00)
windows = {}
min_durs = {}
locs = {}

for name, loc, s_str, e_str, dmin in people:
    s_abs = to_minutes(s_str)
    e_abs = to_minutes(e_str)
    # relative to 09:00 baseline
    s_rel = s_abs - day_start
    e_rel = e_abs - day_start
    windows[name] = (s_rel, e_rel)
    min_durs[name] = dmin
    locs[name] = loc

    meet[name] = Bool(f"meet_{name}")
    start[name] = Int(f"start_{name}")  # minutes from 09:00
    end[name] = Int(f"end_{name}")

    # Base bounds (keep within a reasonable day horizon: 0..(22:00-09:00)=780)
    opt.add(Implies(meet[name], And(start[name] >= 0, start[name] <= 780)))
    opt.add(Implies(meet[name], end[name] == start[name] + dmin))
    # Availability window
    s_rel, e_rel = windows[name]
    opt.add(Implies(meet[name], And(start[name] >= s_rel, end[name] <= e_rel)))
    # Travel from start location if first
    # This is a general lower bound; if they are not first, stronger pairwise constraints will apply.
    opt.add(Implies(meet[name], start[name] >= T[(start_location, locs[name])]))

# Pairwise non-overlap with travel times
names = [p[0] for p in people]
for i in range(len(names)):
    for j in range(i+1, len(names)):
        a = names[i]
        b = names[j]
        # When both are met, enforce travel-time-separated ordering
        tij = T[(locs[a], locs[b])]
        tji = T[(locs[b], locs[a])]
        opt.add(Implies(And(meet[a], meet[b]),
                        Or(end[a] + tij <= start[b],
                           end[b] + tji <= start[a])))

# Objective: maximize number of friends met
total_met = Sum([If(meet[n], 1, 0) for n in names])
h1 = opt.maximize(total_met)

# Optionally, prefer earlier finishing (secondary mild tie-breaker)
latest_end = Int("latest_end")
opt.add(latest_end == If(len(names) == 0, 0, Max(*[If(meet[n], end[n], 0) for n in names])))
h2 = opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit

m = opt.model()

# Extract meetings that are scheduled
meetings = []
for n in names:
    if m.evaluate(meet[n], model_completion=True):
        s = m.evaluate(start[n]).as_long()
        e = m.evaluate(end[n]).as_long()
        # Convert to absolute minutes in day
        s_abs = day_start + s
        e_abs = day_start + e
        meetings.append({
            "action": "meet",
            "person": n,
            "start_time": minutes_to_hhmm(s_abs),
            "end_time": minutes_to_hhmm(e_abs),
        })

# Sort by start time
meetings.sort(key=lambda x: x["start_time"])

# Print JSON itinerary
print(json.dumps({"itinerary": meetings}))