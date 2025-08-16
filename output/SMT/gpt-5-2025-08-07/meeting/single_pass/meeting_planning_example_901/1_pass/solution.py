# Solve the SF day-meetings problem with Z3 and output a JSON itinerary
from z3 import *

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# People data: name, location, availability start, availability end, minimum duration (minutes)
people = [
    ("Emily",    "Pacific Heights",   to_min("09:15"), to_min("13:45"), 120),
    ("Helen",    "North Beach",       to_min("13:45"), to_min("18:45"),  30),
    ("Kimberly", "Golden Gate Park",  to_min("18:45"), to_min("21:15"),  75),
    ("James",    "Embarcadero",       to_min("10:30"), to_min("11:30"),  30),
    ("Linda",    "Haight-Ashbury",    to_min("07:30"), to_min("19:15"),  15),
    ("Paul",     "Fisherman's Wharf", to_min("14:45"), to_min("18:45"),  90),
    ("Anthony",  "Mission District",  to_min("08:00"), to_min("14:45"), 105),
    ("Nancy",    "Alamo Square",      to_min("08:30"), to_min("13:45"), 120),
    ("William",  "Bayview",           to_min("17:30"), to_min("20:30"), 120),
    ("Margaret", "Richmond District", to_min("15:15"), to_min("18:15"),  45),
]

# Travel times (minutes) between neighborhoods, directed
T = {}
def add(a, b, t):
    T[(a, b)] = t

# Fill travel times from prompt
add("Russian Hill","Pacific Heights",7)
add("Russian Hill","North Beach",5)
add("Russian Hill","Golden Gate Park",21)
add("Russian Hill","Embarcadero",8)
add("Russian Hill","Haight-Ashbury",17)
add("Russian Hill","Fisherman's Wharf",7)
add("Russian Hill","Mission District",16)
add("Russian Hill","Alamo Square",15)
add("Russian Hill","Bayview",23)
add("Russian Hill","Richmond District",14)

add("Pacific Heights","Russian Hill",7)
add("Pacific Heights","North Beach",9)
add("Pacific Heights","Golden Gate Park",15)
add("Pacific Heights","Embarcadero",10)
add("Pacific Heights","Haight-Ashbury",11)
add("Pacific Heights","Fisherman's Wharf",13)
add("Pacific Heights","Mission District",15)
add("Pacific Heights","Alamo Square",10)
add("Pacific Heights","Bayview",22)
add("Pacific Heights","Richmond District",12)

add("North Beach","Russian Hill",4)
add("North Beach","Pacific Heights",8)
add("North Beach","Golden Gate Park",22)
add("North Beach","Embarcadero",6)
add("North Beach","Haight-Ashbury",18)
add("North Beach","Fisherman's Wharf",5)
add("North Beach","Mission District",18)
add("North Beach","Alamo Square",16)
add("North Beach","Bayview",25)
add("North Beach","Richmond District",18)

add("Golden Gate Park","Russian Hill",19)
add("Golden Gate Park","Pacific Heights",16)
add("Golden Gate Park","North Beach",23)
add("Golden Gate Park","Embarcadero",25)
add("Golden Gate Park","Haight-Ashbury",7)
add("Golden Gate Park","Fisherman's Wharf",24)
add("Golden Gate Park","Mission District",17)
add("Golden Gate Park","Alamo Square",9)
add("Golden Gate Park","Bayview",23)
add("Golden Gate Park","Richmond District",7)

add("Embarcadero","Russian Hill",8)
add("Embarcadero","Pacific Heights",11)
add("Embarcadero","North Beach",5)
add("Embarcadero","Golden Gate Park",25)
add("Embarcadero","Haight-Ashbury",21)
add("Embarcadero","Fisherman's Wharf",6)
add("Embarcadero","Mission District",20)
add("Embarcadero","Alamo Square",19)
add("Embarcadero","Bayview",21)
add("Embarcadero","Richmond District",21)

add("Haight-Ashbury","Russian Hill",17)
add("Haight-Ashbury","Pacific Heights",12)
add("Haight-Ashbury","North Beach",19)
add("Haight-Ashbury","Golden Gate Park",7)
add("Haight-Ashbury","Embarcadero",20)
add("Haight-Ashbury","Fisherman's Wharf",23)
add("Haight-Ashbury","Mission District",11)
add("Haight-Ashbury","Alamo Square",5)
add("Haight-Ashbury","Bayview",18)
add("Haight-Ashbury","Richmond District",10)

add("Fisherman's Wharf","Russian Hill",7)
add("Fisherman's Wharf","Pacific Heights",12)
add("Fisherman's Wharf","North Beach",6)
add("Fisherman's Wharf","Golden Gate Park",25)
add("Fisherman's Wharf","Embarcadero",8)
add("Fisherman's Wharf","Haight-Ashbury",22)
add("Fisherman's Wharf","Mission District",22)
add("Fisherman's Wharf","Alamo Square",21)
add("Fisherman's Wharf","Bayview",26)
add("Fisherman's Wharf","Richmond District",18)

add("Mission District","Russian Hill",15)
add("Mission District","Pacific Heights",16)
add("Mission District","North Beach",17)
add("Mission District","Golden Gate Park",17)
add("Mission District","Embarcadero",19)
add("Mission District","Haight-Ashbury",12)
add("Mission District","Fisherman's Wharf",22)
add("Mission District","Alamo Square",11)
add("Mission District","Bayview",14)
add("Mission District","Richmond District",20)

add("Alamo Square","Russian Hill",13)
add("Alamo Square","Pacific Heights",10)
add("Alamo Square","North Beach",15)
add("Alamo Square","Golden Gate Park",9)
add("Alamo Square","Embarcadero",16)
add("Alamo Square","Haight-Ashbury",5)
add("Alamo Square","Fisherman's Wharf",19)
add("Alamo Square","Mission District",10)
add("Alamo Square","Bayview",16)
add("Alamo Square","Richmond District",11)

add("Bayview","Russian Hill",23)
add("Bayview","Pacific Heights",23)
add("Bayview","North Beach",22)
add("Bayview","Golden Gate Park",22)
add("Bayview","Embarcadero",19)
add("Bayview","Haight-Ashbury",19)
add("Bayview","Fisherman's Wharf",25)
add("Bayview","Mission District",13)
add("Bayview","Alamo Square",16)
add("Bayview","Richmond District",25)

add("Richmond District","Russian Hill",13)
add("Richmond District","Pacific Heights",10)
add("Richmond District","North Beach",17)
add("Richmond District","Golden Gate Park",9)
add("Richmond District","Embarcadero",19)
add("Richmond District","Haight-Ashbury",10)
add("Richmond District","Fisherman's Wharf",18)
add("Richmond District","Mission District",20)
add("Richmond District","Alamo Square",13)
add("Richmond District","Bayview",27)

origin_loc = "Russian Hill"
origin_time = to_min("09:00")

n = len(people)
name = [p[0] for p in people]
loc  = [p[1] for p in people]
avail_s = [p[2] for p in people]
avail_e = [p[3] for p in people]
min_dur = [p[4] for p in people]

opt = Optimize()

meet = [Bool(f"meet_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end   = [Int(f"end_{i}") for i in range(n)]

# Domain constraints and availability
for i in range(n):
    opt.add(start[i] >= 0, start[i] <= 24*60)
    opt.add(end[i]   >= 0, end[i]   <= 24*60)
    opt.add(end[i] >= start[i])  # non-negative duration always
    # Stay within availability window when meeting; allow slack otherwise
    opt.add(Implies(meet[i], And(start[i] >= avail_s[i], end[i] <= avail_e[i], end[i] - start[i] >= min_dur[i])))
    # To avoid unconstrained times exploding, softly keep times within availability if not meeting
    opt.add(Implies(Not(meet[i]), And(start[i] >= avail_s[i], end[i] <= avail_e[i])))

# Successor variables to build a single chain over the selected meetings
succ = [[Bool(f"succ_{i}_{j}") if i != j else False for j in range(n)] for i in range(n)]

# If succ[i][j] then both are met and travel-time feasibility holds
for i in range(n):
    for j in range(n):
        if i == j: 
            continue
        opt.add(Implies(succ[i][j], And(meet[i], meet[j], end[i] + T[(loc[i], loc[j])] <= start[j])))

# At most one successor and at most one predecessor
for i in range(n):
    opt.add(Sum([If(succ[i][j], 1, 0) for j in range(n) if i != j]) <= 1)
    opt.add(Sum([If(succ[j][i], 1, 0) for j in range(n) if i != j]) <= 1)

# Count of met people and edges
count_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
count_edges = Sum([If(succ[i][j], 1, 0) for i in range(n) for j in range(n) if i != j])

# Head nodes (no predecessor among met)
head = [Bool(f"head_{i}") for i in range(n)]
for i in range(n):
    pred_count_i = Sum([If(succ[j][i], 1, 0) for j in range(n) if j != i])
    # head[i] iff meet[i] and pred_count == 0
    opt.add(Implies(head[i], And(meet[i], pred_count_i == 0)))
    opt.add(Implies(And(meet[i], pred_count_i == 0), head[i]))

head_count = Sum([If(head[i], 1, 0) for i in range(n)])

# Exactly one head if there is at least one meeting; else 0 heads
opt.add(If(count_meet == 0, head_count == 0, head_count == 1))

# Number of edges equals number of nodes minus number of heads (i.e., chain)
opt.add(count_edges == count_meet - head_count)

# Origin feasibility: the head meeting must be reachable from origin at 09:00
for i in range(n):
    opt.add(Implies(head[i], start[i] >= origin_time + T[(origin_loc, loc[i])]))

# Objective: maximize the number of friends met
opt.maximize(count_meet)

# (Optional) tie-breaker: maximize total meeting time
total_meet_minutes = Sum([If(meet[i], end[i] - start[i], 0) for i in range(n)])
opt.maximize(total_meet_minutes)

# Solve
if opt.check() != sat:
    # No feasible plan; output empty itinerary
    print({"itinerary": []})
else:
    model = opt.model()
    meetings = []
    for i in range(n):
        if is_true(model.eval(meet[i])):
            s = model.eval(start[i]).as_long()
            e = model.eval(end[i]).as_long()
            meetings.append((s, e, name[i]))
    # Sort by start time (chronological order)
    meetings.sort(key=lambda x: x[0])

    itinerary = []
    for s, e, nm in meetings:
        itinerary.append({
            "action": "meet",
            "person": nm,
            "start_time": to_str(s),
            "end_time": to_str(e),
        })
    print({"itinerary": itinerary})