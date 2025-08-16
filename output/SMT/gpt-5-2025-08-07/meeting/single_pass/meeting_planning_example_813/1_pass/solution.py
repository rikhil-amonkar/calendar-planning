# Requires: z3-solver (pip install z3-solver)
# This program models and solves the described scheduling problem with Z3 and prints
# a JSON itinerary that maximizes the number of friends met while respecting travel times
# and availability windows.

from z3 import *
import json

# Minutes helper
def hm(h, m): return 60*h + m
def to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Districts (keys as given in prompt)
D = [
    "Marina District",
    "Embarcadero",
    "Bayview",
    "Union Square",
    "Chinatown",
    "Sunset District",
    "Golden Gate Park",
    "Financial District",
    "Haight-Ashbury",
    "Mission District"
]

# Directed travel times (minutes), exactly as provided
T = {d:{} for d in D}
def setT(a,b,t): T[a][b]=t

setT("Marina District","Embarcadero",14)
setT("Marina District","Bayview",27)
setT("Marina District","Union Square",16)
setT("Marina District","Chinatown",15)
setT("Marina District","Sunset District",19)
setT("Marina District","Golden Gate Park",18)
setT("Marina District","Financial District",17)
setT("Marina District","Haight-Ashbury",16)
setT("Marina District","Mission District",20)

setT("Embarcadero","Marina District",12)
setT("Embarcadero","Bayview",21)
setT("Embarcadero","Union Square",10)
setT("Embarcadero","Chinatown",7)
setT("Embarcadero","Sunset District",30)
setT("Embarcadero","Golden Gate Park",25)
setT("Embarcadero","Financial District",5)
setT("Embarcadero","Haight-Ashbury",21)
setT("Embarcadero","Mission District",20)

setT("Bayview","Marina District",27)
setT("Bayview","Embarcadero",19)
setT("Bayview","Union Square",18)
setT("Bayview","Chinatown",19)
setT("Bayview","Sunset District",23)
setT("Bayview","Golden Gate Park",22)
setT("Bayview","Financial District",19)
setT("Bayview","Haight-Ashbury",19)
setT("Bayview","Mission District",13)

setT("Union Square","Marina District",18)
setT("Union Square","Embarcadero",11)
setT("Union Square","Bayview",15)
setT("Union Square","Chinatown",7)
setT("Union Square","Sunset District",27)
setT("Union Square","Golden Gate Park",22)
setT("Union Square","Financial District",9)
setT("Union Square","Haight-Ashbury",18)
setT("Union Square","Mission District",14)

setT("Chinatown","Marina District",12)
setT("Chinatown","Embarcadero",5)
setT("Chinatown","Bayview",20)
setT("Chinatown","Union Square",7)
setT("Chinatown","Sunset District",29)
setT("Chinatown","Golden Gate Park",23)
setT("Chinatown","Financial District",5)
setT("Chinatown","Haight-Ashbury",19)
setT("Chinatown","Mission District",17)

setT("Sunset District","Marina District",21)
setT("Sunset District","Embarcadero",30)
setT("Sunset District","Bayview",22)
setT("Sunset District","Union Square",30)
setT("Sunset District","Chinatown",30)
setT("Sunset District","Golden Gate Park",11)
setT("Sunset District","Financial District",30)
setT("Sunset District","Haight-Ashbury",15)
setT("Sunset District","Mission District",25)

setT("Golden Gate Park","Marina District",16)
setT("Golden Gate Park","Embarcadero",25)
setT("Golden Gate Park","Bayview",23)
setT("Golden Gate Park","Union Square",22)
setT("Golden Gate Park","Chinatown",23)
setT("Golden Gate Park","Sunset District",10)
setT("Golden Gate Park","Financial District",26)
setT("Golden Gate Park","Haight-Ashbury",7)
setT("Golden Gate Park","Mission District",17)

setT("Financial District","Marina District",15)
setT("Financial District","Embarcadero",4)
setT("Financial District","Bayview",19)
setT("Financial District","Union Square",9)
setT("Financial District","Chinatown",5)
setT("Financial District","Sunset District",30)
setT("Financial District","Golden Gate Park",23)
setT("Financial District","Haight-Ashbury",19)
setT("Financial District","Mission District",17)

setT("Haight-Ashbury","Marina District",17)
setT("Haight-Ashbury","Embarcadero",20)
setT("Haight-Ashbury","Bayview",18)
setT("Haight-Ashbury","Union Square",19)
setT("Haight-Ashbury","Chinatown",19)
setT("Haight-Ashbury","Sunset District",15)
setT("Haight-Ashbury","Golden Gate Park",7)
setT("Haight-Ashbury","Financial District",21)
setT("Haight-Ashbury","Mission District",11)

setT("Mission District","Marina District",19)
setT("Mission District","Embarcadero",19)
setT("Mission District","Bayview",14)
setT("Mission District","Union Square",15)
setT("Mission District","Chinatown",16)
setT("Mission District","Sunset District",24)
setT("Mission District","Golden Gate Park",17)
setT("Mission District","Financial District",15)
setT("Mission District","Haight-Ashbury",12)

# People data
people = [
    {"name":"Joshua",   "loc":"Embarcadero",       "avail":(hm(9,45),  hm(18,0)),  "min_dur":105},
    {"name":"Jeffrey",  "loc":"Bayview",           "avail":(hm(9,45),  hm(20,15)), "min_dur":75},
    {"name":"Charles",  "loc":"Union Square",      "avail":(hm(10,45), hm(20,15)), "min_dur":120},
    {"name":"Joseph",   "loc":"Chinatown",         "avail":(hm(7,0),   hm(15,30)), "min_dur":60},
    {"name":"Elizabeth","loc":"Sunset District",   "avail":(hm(9,0),   hm(9,45)),  "min_dur":45},
    {"name":"Matthew",  "loc":"Golden Gate Park",  "avail":(hm(11,0),  hm(19,30)), "min_dur":45},
    {"name":"Carol",    "loc":"Financial District","avail":(hm(10,45), hm(11,15)), "min_dur":15},
    {"name":"Paul",     "loc":"Haight-Ashbury",    "avail":(hm(19,15), hm(20,30)), "min_dur":15},
    {"name":"Rebecca",  "loc":"Mission District",  "avail":(hm(17,0),  hm(21,45)), "min_dur":45},
]

# Start info
start_loc = "Marina District"
start_time = hm(9,0)

# Z3 model
opt = Optimize()
opt.set(priority='lex')  # maximize count first, then secondary objectives

n = len(people)
start_vars = [Int(f"start_{i}") for i in range(n)]
end_vars   = [Int(f"end_{i}")   for i in range(n)]
meet_vars  = [Bool(f"meet_{i}") for i in range(n)]

# Variable bounds and meeting window/duration constraints
for i,p in enumerate(people):
    s, e = start_vars[i], end_vars[i]
    avail_start, avail_end = p["avail"]
    min_dur = p["min_dur"]
    # Time domain
    opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)
    # If meeting, must be within availability and meet minimum duration
    opt.add(Implies(meet_vars[i], And(s >= avail_start,
                                      e <= avail_end,
                                      e - s >= min_dur)))
    # If not meeting, set zero-length to avoid interfering in max constraints
    opt.add(Implies(Not(meet_vars[i]), e == s))
    # Earliest possible start given starting location travel
    opt.add(Implies(meet_vars[i], s >= start_time + T[start_loc][p["loc"]]))

# Pairwise ordering / travel-feasible separation if both are met
for i in range(n):
    for j in range(i+1, n):
        li = people[i]["loc"]
        lj = people[j]["loc"]
        travel_ij = T[li][lj]
        travel_ji = T[lj][li]
        # If both met: either i before j with travel, or j before i with travel
        opt.add(Or(Not(meet_vars[i]),
                   Not(meet_vars[j]),
                   end_vars[i] + travel_ij <= start_vars[j],
                   end_vars[j] + travel_ji <= start_vars[i]))

# Objectives
# 1) Maximize number of friends met
num_met = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
opt.maximize(num_met)

# 2) Minimize makespan (last end time)
last_end = Int("last_end")
opt.add(last_end >= start_time)  # at least day start
for i in range(n):
    opt.add(last_end >= end_vars[i])
opt.minimize(last_end)

# 3) Minimize sum of starts for met meetings (earlier starts preferred)
sum_starts_met = Sum([If(meet_vars[i], start_vars[i], 0) for i in range(n)])
opt.minimize(sum_starts_met)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()

    # Collect met meetings
    meetings = []
    for i,p in enumerate(people):
        if is_true(m.eval(meet_vars[i])):
            s = m.eval(start_vars[i]).as_long()
            e = m.eval(end_vars[i]).as_long()
            meetings.append({
                "action": "meet",
                "person": p["name"],
                "start_time": to_hhmm(s),
                "end_time": to_hhmm(e),
                "_start_min": s  # for sorting
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["_start_min"])
    for mt in meetings:
        del mt["_start_min"]

    print(json.dumps({"itinerary": meetings}, ensure_ascii=False))