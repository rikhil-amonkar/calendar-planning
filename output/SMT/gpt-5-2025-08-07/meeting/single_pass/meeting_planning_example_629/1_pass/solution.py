# Solve the SF day meetup scheduling problem with Z3 and output a JSON itinerary.
# Objective: maximize the number of friends met subject to availability, travel, and minimum meeting durations.

from z3 import *
import json

def parse_time_24h_str(s):
    # s is like "11:00", "21:15" already in 24-hour format per prompt
    h, m = map(int, s.split(":"))
    return h * 60 + m

def minutes_to_HHMM(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Build directed travel time matrix (minutes) as provided
locs = [
    "Russian Hill", "Presidio", "Chinatown", "Pacific Heights",
    "Richmond District", "Fisherman's Wharf", "Golden Gate Park", "Bayview"
]

travel = {u: {} for u in locs}

def set_t(u, v, t):
    travel[u][v] = t

# Russian Hill to ...
set_t("Russian Hill", "Presidio", 14)
set_t("Russian Hill", "Chinatown", 9)
set_t("Russian Hill", "Pacific Heights", 7)
set_t("Russian Hill", "Richmond District", 14)
set_t("Russian Hill", "Fisherman's Wharf", 7)
set_t("Russian Hill", "Golden Gate Park", 21)
set_t("Russian Hill", "Bayview", 23)

# Presidio to ...
set_t("Presidio", "Russian Hill", 14)
set_t("Presidio", "Chinatown", 21)
set_t("Presidio", "Pacific Heights", 11)
set_t("Presidio", "Richmond District", 7)
set_t("Presidio", "Fisherman's Wharf", 19)
set_t("Presidio", "Golden Gate Park", 12)
set_t("Presidio", "Bayview", 31)

# Chinatown to ...
set_t("Chinatown", "Russian Hill", 7)
set_t("Chinatown", "Presidio", 19)
set_t("Chinatown", "Pacific Heights", 10)
set_t("Chinatown", "Richmond District", 20)
set_t("Chinatown", "Fisherman's Wharf", 8)
set_t("Chinatown", "Golden Gate Park", 23)
set_t("Chinatown", "Bayview", 22)

# Pacific Heights to ...
set_t("Pacific Heights", "Russian Hill", 7)
set_t("Pacific Heights", "Presidio", 11)
set_t("Pacific Heights", "Chinatown", 11)
set_t("Pacific Heights", "Richmond District", 12)
set_t("Pacific Heights", "Fisherman's Wharf", 13)
set_t("Pacific Heights", "Golden Gate Park", 15)
set_t("Pacific Heights", "Bayview", 22)

# Richmond District to ...
set_t("Richmond District", "Russian Hill", 13)
set_t("Richmond District", "Presidio", 7)
set_t("Richmond District", "Chinatown", 20)
set_t("Richmond District", "Pacific Heights", 10)
set_t("Richmond District", "Fisherman's Wharf", 18)
set_t("Richmond District", "Golden Gate Park", 9)
set_t("Richmond District", "Bayview", 26)

# Fisherman's Wharf to ...
set_t("Fisherman's Wharf", "Russian Hill", 7)
set_t("Fisherman's Wharf", "Presidio", 17)
set_t("Fisherman's Wharf", "Chinatown", 12)
set_t("Fisherman's Wharf", "Pacific Heights", 12)
set_t("Fisherman's Wharf", "Richmond District", 18)
set_t("Fisherman's Wharf", "Golden Gate Park", 25)
set_t("Fisherman's Wharf", "Bayview", 26)

# Golden Gate Park to ...
set_t("Golden Gate Park", "Russian Hill", 19)
set_t("Golden Gate Park", "Presidio", 11)
set_t("Golden Gate Park", "Chinatown", 23)
set_t("Golden Gate Park", "Pacific Heights", 16)
set_t("Golden Gate Park", "Richmond District", 7)
set_t("Golden Gate Park", "Fisherman's Wharf", 24)
set_t("Golden Gate Park", "Bayview", 23)

# Bayview to ...
set_t("Bayview", "Russian Hill", 23)
set_t("Bayview", "Presidio", 31)
set_t("Bayview", "Chinatown", 18)
set_t("Bayview", "Pacific Heights", 23)
set_t("Bayview", "Richmond District", 25)
set_t("Bayview", "Fisherman's Wharf", 25)
set_t("Bayview", "Golden Gate Park", 22)

# Friends data
friends = [
    # name, location, availability_start, availability_end, min_duration (minutes)
    ("Matthew",  "Presidio",            parse_time_24h_str("11:00"), parse_time_24h_str("21:00"), 90),
    ("Margaret", "Chinatown",           parse_time_24h_str("09:15"), parse_time_24h_str("18:45"), 90),
    ("Nancy",    "Pacific Heights",     parse_time_24h_str("14:15"), parse_time_24h_str("17:00"), 15),
    ("Helen",    "Richmond District",   parse_time_24h_str("19:45"), parse_time_24h_str("22:00"), 60),
    ("Rebecca",  "Fisherman's Wharf",   parse_time_24h_str("21:15"), parse_time_24h_str("22:15"), 60),
    ("Kimberly", "Golden Gate Park",    parse_time_24h_str("13:00"), parse_time_24h_str("16:30"), 120),
    ("Kenneth",  "Bayview",             parse_time_24h_str("14:30"), parse_time_24h_str("18:00"), 60),
]

# Add a dummy "start" node representing arriving at Russian Hill at 09:00 with zero duration.
start_time = parse_time_24h_str("09:00")
start_node = {
    "name": "_START_",
    "location": "Russian Hill",
    "avail_start": start_time,
    "avail_end": start_time,
    "min_duration": 0
}

nodes = [start_node] + [
    {
        "name": nm,
        "location": loc,
        "avail_start": a0,
        "avail_end": a1,
        "min_duration": mindur
    }
    for (nm, loc, a0, a1, mindur) in friends
]

N = len(nodes)
# Z3 variables
s = [Int(f"s_{i}") for i in range(N)]
e = [Int(f"e_{i}") for i in range(N)]
sel = [Bool(f"sel_{i}") for i in range(N)]

opt = Optimize()

# Bounds for all times
for i in range(N):
    opt.add(s[i] >= 0, s[i] <= 24*60, e[i] >= 0, e[i] <= 24*60)

# Start node constraints
opt.add(sel[0] == True)
opt.add(s[0] == start_node["avail_start"])
opt.add(e[0] == start_node["avail_end"])

# Constraints for each real meeting (i >= 1)
for i in range(1, N):
    node = nodes[i]
    a0 = node["avail_start"]
    a1 = node["avail_end"]
    mind = node["min_duration"]

    # If selected, must honor availability and min duration
    opt.add(Implies(sel[i], And(s[i] >= a0, e[i] <= a1, e[i] - s[i] >= mind)))
    # If not selected, pin to availability start (zero duration)
    opt.add(Implies(Not(sel[i]), And(s[i] == a0, e[i] == a0)))

# Travel feasibility and no overlap: for any two selected nodes i, j, one must precede the other with travel time
def t(i, j):
    loc_i = nodes[i]["location"]
    loc_j = nodes[j]["location"]
    return travel[loc_i][loc_j]

for i in range(N):
    for j in range(i+1, N):
        tij = t(i, j)
        tji = t(j, i)
        opt.add(Implies(And(sel[i], sel[j]), Or(e[i] + tij <= s[j], e[j] + tji <= s[i])))

# Objective: maximize the number of friends met (exclude start node at index 0)
count_met = Sum([If(sel[i], 1, 0) for i in range(1, N)])
opt.maximize(count_met)

# Secondary objective: minimize total meeting time (push toward minimum durations)
total_meet_minutes = Sum([If(sel[i], e[i] - s[i], 0) for i in range(1, N)])
opt.minimize(total_meet_minutes)

if opt.check() != sat:
    # No solution found; output empty itinerary
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()

    # Extract selected meetings and sort by start time
    meetings = []
    for i in range(1, N):
        if is_true(m.eval(sel[i])):
            start_min = m.eval(s[i]).as_long()
            end_min = m.eval(e[i]).as_long()
            meetings.append((start_min, end_min, nodes[i]["name"]))

    meetings.sort(key=lambda x: x[0])

    itinerary = []
    for st, en, person in meetings:
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": minutes_to_HHMM(st),
            "end_time": minutes_to_HHMM(en)
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))