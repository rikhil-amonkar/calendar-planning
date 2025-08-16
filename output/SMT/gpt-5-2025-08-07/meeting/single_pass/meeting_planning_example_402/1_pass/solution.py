# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat
import json

def hhmm_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Locations
GGP = "Golden Gate Park"
HA = "Haight-Ashbury"
SD = "Sunset District"
MD = "Marina District"
FD = "Financial District"
US = "Union Square"

locs = [GGP, HA, SD, MD, FD, US]

# Travel times (minutes), directional as given
travel = {}
def T(a,b,t):
    travel[(a,b)] = t

# Given distances
T(GGP, HA, 7);  T(GGP, SD, 10); T(GGP, MD, 16); T(GGP, FD, 26); T(GGP, US, 22)
T(HA,  GGP, 7); T(HA,  SD, 15); T(HA,  MD, 17); T(HA,  FD, 21); T(HA,  US, 17)
T(SD,  GGP, 11);T(SD,  HA, 15); T(SD,  MD, 21); T(SD,  FD, 30); T(SD,  US, 30)
T(MD,  GGP, 18);T(MD,  HA, 16); T(MD,  SD, 19); T(MD,  FD, 17); T(MD,  US, 16)
T(FD,  GGP, 23);T(FD,  HA, 19); T(FD,  SD, 31); T(FD,  MD, 15); T(FD,  US, 9)
T(US,  GGP, 22);T(US,  HA, 18); T(US,  SD, 26); T(US,  MD, 18); T(US,  FD, 9)

# Zero travel to self
for a in locs:
    travel[(a,a)] = 0

# Friends data: name, location, availability start/end, minimum duration (minutes)
friends = [
    # name,     location,        start,   end,    min_dur
    ("Sarah",    HA,             "17:00", "21:30", 105),
    ("Patricia", SD,             "17:00", "19:45", 45),
    ("Matthew",  MD,             "09:15", "12:00", 15),
    ("Joseph",   FD,             "14:15", "18:45", 30),
    ("Robert",   US,             "10:15", "21:45", 15),
]

# Convert availability to minutes from midnight
friends_data = []
for name, loc, s, e, d in friends:
    friends_data.append({
        "name": name,
        "loc": loc,
        "start": hhmm_to_min(s),
        "end": hhmm_to_min(e),
        "min_dur": d
    })

# Start at Golden Gate Park at 09:00
day_start = hhmm_to_min("09:00")
start_loc = GGP

opt = Optimize()

# Variables per friend
vars_map = {}
for f in friends_data:
    name = f["name"]
    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    meet = Bool(f"meet_{name}")
    x = Int(f"x_{name}")  # 0/1 indicator
    # Bounds for times (keep within a reasonable day)
    opt.add(s >= day_start, s <= hhmm_to_min("23:59"))
    opt.add(e >= day_start, e <= hhmm_to_min("23:59"))
    # Link indicator and boolean
    opt.add(If(meet, x == 1, x == 0) == True)
    # Availability and duration constraints only if meeting
    opt.add(Implies(meet, And(
        s >= f["start"],
        e <= f["end"],
        e - s >= f["min_dur"]
    )))
    # If not meeting, keep a sane relation (zero-length allowed)
    opt.add(Implies(~meet, e == s))
    # Must be reachable from the starting point at 09:00
    opt.add(Implies(meet, s >= day_start + travel[(start_loc, f["loc"])]))
    vars_map[name] = {"s": s, "e": e, "meet": meet, "x": x, "loc": f["loc"]}

# Non-overlap with travel times between any two met friends
names = [f["name"] for f in friends_data]
for i in range(len(names)):
    for j in range(i+1, len(names)):
        ni, nj = names[i], names[j]
        si, ei, li = vars_map[ni]["s"], vars_map[ni]["e"], vars_map[ni]["loc"]
        sj, ej, lj = vars_map[nj]["s"], vars_map[nj]["e"], vars_map[nj]["loc"]
        mi, mj = vars_map[ni]["meet"], vars_map[nj]["meet"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        opt.add(Implies(And(mi, mj), Or(
            ei + tij <= sj,
            ej + tji <= si
        )))

# Objective 1: maximize number of friends met
opt.maximize(Sum([vars_map[n]["x"] for n in names]))
# Objective 2: minimize total durations (push to minimum durations once count is maximized)
opt.minimize(Sum([vars_map[n]["e"] - vars_map[n]["s"] for n in names]))
# Objective 3: minimize sum of start times (push meetings as early as feasible)
opt.minimize(Sum([vars_map[n]["s"] for n in names]))

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    meetings = []
    for n in names:
        if m.eval(vars_map[n]["x"]).as_long() == 1:
            s = m.eval(vars_map[n]["s"]).as_long()
            e = m.eval(vars_map[n]["e"]).as_long()
            meetings.append({
                "action": "meet",
                "person": n,
                "start": min_to_hhmm(s),
                "end": min_to_hhmm(e)
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start"])
    print(json.dumps({"itinerary": meetings}))