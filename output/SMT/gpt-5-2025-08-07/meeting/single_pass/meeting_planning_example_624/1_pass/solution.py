# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, Implies
import json

def time_to_min(t):
    # t like "9:00AM" or "21:30"
    t = t.strip().upper()
    if t.endswith("AM") or t.endswith("PM"):
        ampm = t[-2:]
        hhmm = t[:-2]
        hh, mm = map(int, hhmm.split(":"))
        if ampm == "AM":
            if hh == 12:
                hh = 0
        else:
            if hh != 12:
                hh += 12
        return hh * 60 + mm
    else:
        hh, mm = map(int, t.split(":"))
        return hh * 60 + mm

def min_to_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Data
start_location = "Golden Gate Park"
arrival_time = time_to_min("9:00AM")

friends = [
    # name, location, availability start, availability end, minimum minutes
    ("Carol", "Haight-Ashbury", time_to_min("9:30PM"), time_to_min("10:30PM"), 60),
    ("Laura", "Fisherman's Wharf", time_to_min("11:45AM"), time_to_min("9:30PM"), 60),
    ("Karen", "The Castro", time_to_min("7:15AM"), time_to_min("2:00PM"), 75),
    ("Elizabeth", "Chinatown", time_to_min("12:15PM"), time_to_min("9:30PM"), 75),
    ("Deborah", "Alamo Square", time_to_min("12:00PM"), time_to_min("3:00PM"), 105),
    ("Jason", "North Beach", time_to_min("2:45PM"), time_to_min("7:00PM"), 90),
    ("Steven", "Russian Hill", time_to_min("2:45PM"), time_to_min("6:30PM"), 120),
]

# Travel times (directed, minutes)
travel = {}
def T(a,b,v):
    travel[(a,b)] = v

# From Golden Gate Park
T("Golden Gate Park","Haight-Ashbury",7)
T("Golden Gate Park","Fisherman's Wharf",24)
T("Golden Gate Park","The Castro",13)
T("Golden Gate Park","Chinatown",23)
T("Golden Gate Park","Alamo Square",10)
T("Golden Gate Park","North Beach",24)
T("Golden Gate Park","Russian Hill",19)

# From Haight-Ashbury
T("Haight-Ashbury","Golden Gate Park",7)
T("Haight-Ashbury","Fisherman's Wharf",23)
T("Haight-Ashbury","The Castro",6)
T("Haight-Ashbury","Chinatown",19)
T("Haight-Ashbury","Alamo Square",5)
T("Haight-Ashbury","North Beach",19)
T("Haight-Ashbury","Russian Hill",17)

# From Fisherman's Wharf
T("Fisherman's Wharf","Golden Gate Park",25)
T("Fisherman's Wharf","Haight-Ashbury",22)
T("Fisherman's Wharf","The Castro",26)
T("Fisherman's Wharf","Chinatown",12)
T("Fisherman's Wharf","Alamo Square",20)
T("Fisherman's Wharf","North Beach",6)
T("Fisherman's Wharf","Russian Hill",7)

# From The Castro
T("The Castro","Golden Gate Park",11)
T("The Castro","Haight-Ashbury",6)
T("The Castro","Fisherman's Wharf",24)
T("The Castro","Chinatown",20)
T("The Castro","Alamo Square",8)
T("The Castro","North Beach",20)
T("The Castro","Russian Hill",18)

# From Chinatown
T("Chinatown","Golden Gate Park",23)
T("Chinatown","Haight-Ashbury",19)
T("Chinatown","Fisherman's Wharf",8)
T("Chinatown","The Castro",22)
T("Chinatown","Alamo Square",17)
T("Chinatown","North Beach",3)
T("Chinatown","Russian Hill",7)

# From Alamo Square
T("Alamo Square","Golden Gate Park",9)
T("Alamo Square","Haight-Ashbury",5)
T("Alamo Square","Fisherman's Wharf",19)
T("Alamo Square","The Castro",8)
T("Alamo Square","Chinatown",16)
T("Alamo Square","North Beach",15)
T("Alamo Square","Russian Hill",13)

# From North Beach
T("North Beach","Golden Gate Park",22)
T("North Beach","Haight-Ashbury",18)
T("North Beach","Fisherman's Wharf",5)
T("North Beach","The Castro",22)
T("North Beach","Chinatown",6)
T("North Beach","Alamo Square",16)
T("North Beach","Russian Hill",4)

# From Russian Hill
T("Russian Hill","Golden Gate Park",21)
T("Russian Hill","Haight-Ashbury",17)
T("Russian Hill","Fisherman's Wharf",7)
T("Russian Hill","The Castro",21)
T("Russian Hill","Chinatown",9)
T("Russian Hill","Alamo Square",15)
T("Russian Hill","North Beach",5)

# Build model
n = len(friends)
names = [f[0] for f in friends]
locs = [f[1] for f in friends]
avail_starts = [f[2] for f in friends]
avail_ends = [f[3] for f in friends]
mins_required = [f[4] for f in friends]

# Sanity: ensure travel from start to each location exists
for L in set(locs):
    if (start_location, L) not in travel:
        raise RuntimeError(f"Missing travel time from {start_location} to {L}")

opt = Optimize()
opt.set(priority='lex')

meet = [Bool(f"meet_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end = [Int(f"end_{i}") for i in range(n)]
dur = [Int(f"dur_{i}") for i in range(n)]

# Bounds for all time variables
DAY_LOW = 0
DAY_HIGH = 24*60 + 600  # generous upper bound
for i in range(n):
    opt.add(start[i] >= DAY_LOW, start[i] <= DAY_HIGH)
    opt.add(end[i] >= DAY_LOW, end[i] <= DAY_HIGH)
    opt.add(dur[i] == end[i] - start[i])
    # If we meet, enforce availability, minimum duration, not before 9:00 arrival,
    # and reachable from starting point at 09:00 (baseline constraint).
    opt.add(Implies(meet[i], And(
        start[i] >= max(avail_starts[i], arrival_time),
        end[i] <= avail_ends[i],
        dur[i] >= mins_required[i],
        start[i] >= arrival_time + travel[(start_location, locs[i])]
    )))
    # If we don't meet, we can set a degenerate 0-length or unconstrained interval;
    # nothing else needed.

# Pairwise non-overlapping with travel
order = {}
for i in range(n):
    for j in range(i+1, n):
        order[(i,j)] = Bool(f"order_{i}_before_{j}")
        tij = travel[(locs[i], locs[j])]
        tji = travel[(locs[j], locs[i])]
        # If both are met and i before j, j starts after i ends + travel i->j
        opt.add(Implies(And(meet[i], meet[j], order[(i,j)]), start[j] >= end[i] + tij))
        # If both are met and j before i, i starts after j ends + travel j->i
        opt.add(Implies(And(meet[i], meet[j], Not(order[(i,j)])), start[i] >= end[j] + tji))

# Objectives:
# 1) Maximize number of friends met
count_met = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.maximize(count_met)
# 2) Maximize total meeting time (tie-breaker)
total_meeting_time = Sum([If(meet[i], dur[i], 0) for i in range(n)])
opt.maximize(total_meeting_time)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit(0)

m = opt.model()

meetings = []
for i in range(n):
    if m.evaluate(meet[i], model_completion=True):
        s = m.evaluate(start[i]).as_long()
        e = m.evaluate(end[i]).as_long()
        meetings.append((s, {
            "action": "meet",
            "person": names[i],
            "start_time": min_to_time(s),
            "end_time": min_to_time(e),
        }))

meetings.sort(key=lambda x: x[0])
itinerary = [entry for _, entry in meetings]

print(json.dumps({"itinerary": itinerary}))