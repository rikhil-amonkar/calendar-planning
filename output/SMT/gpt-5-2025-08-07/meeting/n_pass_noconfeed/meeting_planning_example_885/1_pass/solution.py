import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Data
locations = [
    "Russian Hill",
    "Marina District",
    "Financial District",
    "Alamo Square",
    "Golden Gate Park",
    "The Castro",
    "Bayview",
    "Sunset District",
    "Haight-Ashbury",
    "Nob Hill",
]

# Directed travel times in minutes
T = {}
def set_t(a,b,mins):
    T[(a,b)] = mins

set_t("Russian Hill","Marina District",7)
set_t("Russian Hill","Financial District",11)
set_t("Russian Hill","Alamo Square",15)
set_t("Russian Hill","Golden Gate Park",21)
set_t("Russian Hill","The Castro",21)
set_t("Russian Hill","Bayview",23)
set_t("Russian Hill","Sunset District",23)
set_t("Russian Hill","Haight-Ashbury",17)
set_t("Russian Hill","Nob Hill",5)

set_t("Marina District","Russian Hill",8)
set_t("Marina District","Financial District",17)
set_t("Marina District","Alamo Square",15)
set_t("Marina District","Golden Gate Park",18)
set_t("Marina District","The Castro",22)
set_t("Marina District","Bayview",27)
set_t("Marina District","Sunset District",19)
set_t("Marina District","Haight-Ashbury",16)
set_t("Marina District","Nob Hill",12)

set_t("Financial District","Russian Hill",11)
set_t("Financial District","Marina District",15)
set_t("Financial District","Alamo Square",17)
set_t("Financial District","Golden Gate Park",23)
set_t("Financial District","The Castro",20)
set_t("Financial District","Bayview",19)
set_t("Financial District","Sunset District",30)
set_t("Financial District","Haight-Ashbury",19)
set_t("Financial District","Nob Hill",8)

set_t("Alamo Square","Russian Hill",13)
set_t("Alamo Square","Marina District",15)
set_t("Alamo Square","Financial District",17)
set_t("Alamo Square","Golden Gate Park",9)
set_t("Alamo Square","The Castro",8)
set_t("Alamo Square","Bayview",16)
set_t("Alamo Square","Sunset District",16)
set_t("Alamo Square","Haight-Ashbury",5)
set_t("Alamo Square","Nob Hill",11)

set_t("Golden Gate Park","Russian Hill",19)
set_t("Golden Gate Park","Marina District",16)
set_t("Golden Gate Park","Financial District",26)
set_t("Golden Gate Park","Alamo Square",9)
set_t("Golden Gate Park","The Castro",13)
set_t("Golden Gate Park","Bayview",23)
set_t("Golden Gate Park","Sunset District",10)
set_t("Golden Gate Park","Haight-Ashbury",7)
set_t("Golden Gate Park","Nob Hill",20)

set_t("The Castro","Russian Hill",18)
set_t("The Castro","Marina District",21)
set_t("The Castro","Financial District",21)
set_t("The Castro","Alamo Square",8)
set_t("The Castro","Golden Gate Park",11)
set_t("The Castro","Bayview",19)
set_t("The Castro","Sunset District",17)
set_t("The Castro","Haight-Ashbury",6)
set_t("The Castro","Nob Hill",16)

set_t("Bayview","Russian Hill",23)
set_t("Bayview","Marina District",27)
set_t("Bayview","Financial District",19)
set_t("Bayview","Alamo Square",16)
set_t("Bayview","Golden Gate Park",22)
set_t("Bayview","The Castro",19)
set_t("Bayview","Sunset District",23)
set_t("Bayview","Haight-Ashbury",19)
set_t("Bayview","Nob Hill",20)

set_t("Sunset District","Russian Hill",24)
set_t("Sunset District","Marina District",21)
set_t("Sunset District","Financial District",30)
set_t("Sunset District","Alamo Square",17)
set_t("Sunset District","Golden Gate Park",11)
set_t("Sunset District","The Castro",17)
set_t("Sunset District","Bayview",22)
set_t("Sunset District","Haight-Ashbury",15)
set_t("Sunset District","Nob Hill",27)

set_t("Haight-Ashbury","Russian Hill",17)
set_t("Haight-Ashbury","Marina District",17)
set_t("Haight-Ashbury","Financial District",21)
set_t("Haight-Ashbury","Alamo Square",5)
set_t("Haight-Ashbury","Golden Gate Park",7)
set_t("Haight-Ashbury","The Castro",6)
set_t("Haight-Ashbury","Bayview",18)
set_t("Haight-Ashbury","Sunset District",15)
set_t("Haight-Ashbury","Nob Hill",15)

set_t("Nob Hill","Russian Hill",5)
set_t("Nob Hill","Marina District",11)
set_t("Nob Hill","Financial District",9)
set_t("Nob Hill","Alamo Square",11)
set_t("Nob Hill","Golden Gate Park",17)
set_t("Nob Hill","The Castro",17)
set_t("Nob Hill","Bayview",19)
set_t("Nob Hill","Sunset District",24)
set_t("Nob Hill","Haight-Ashbury",13)

def travel(a, b):
    return T[(a, b)]

# People and constraints
people = [
    # name, location, start, end, min_dur (minutes since midnight)
    ("Mark", "Marina District", minutes(18,45), minutes(21,0), 90),
    ("Karen", "Financial District", minutes(9,30), minutes(12,45), 90),
    ("Barbara", "Alamo Square", minutes(10,0), minutes(19,30), 90),
    ("Nancy", "Golden Gate Park", minutes(16,45), minutes(20,0), 105),
    ("David", "The Castro", minutes(9,0), minutes(18,0), 120),
    ("Linda", "Bayview", minutes(18,15), minutes(19,45), 45),
    ("Kevin", "Sunset District", minutes(10,0), minutes(17,45), 120),
    ("Matthew", "Haight-Ashbury", minutes(10,15), minutes(15,30), 45),
    ("Andrew", "Nob Hill", minutes(11,45), minutes(16,45), 105),
]

n = len(people)
start_location = "Russian Hill"
day_start = minutes(9,0)
day_end = minutes(21,0)

# Z3 variables
s = [Int(f"s_{i}") for i in range(n)]  # start time
e = [Int(f"e_{i}") for i in range(n)]  # end time
meet = [Bool(f"meet_{i}") for i in range(n)]
pos = [Int(f"pos_{i}") for i in range(n)]  # position in sequence or -1 if not met
at = [Int(f"at_{p}") for p in range(n)]    # who is at position p, -1 if unused

opt = Optimize()

# Domain constraints and person-specific constraints
for i, (name, loc, w_start, w_end, min_dur) in enumerate(people):
    # Time domains
    opt.add(s[i] >= day_start, s[i] <= day_end)
    opt.add(e[i] >= day_start, e[i] <= day_end)
    # Meeting constraints if met
    opt.add(Implies(meet[i], And(
        s[i] >= w_start,
        e[i] <= w_end,
        e[i] - s[i] >= min_dur,
        pos[i] >= 0, pos[i] < n
    )))
    # If not met, collapse times and pos = -1
    opt.add(Implies(Not(meet[i]), And(e[i] == s[i], pos[i] == -1)))

# Position mapping constraints
for p in range(n):
    # at[p] is either -1 or a valid person index
    opt.add(Or(at[p] == -1, And(at[p] >= 0, at[p] < n)))
    # If a person is placed at p, it must be consistent with meet[] and pos[]
    # (expand with disjunction over people indices)
    opt.add(Or(
        at[p] == -1,
        Or([And(at[p] == i, meet[i], pos[i] == p) for i in range(n)])
    ))

# If person i is met and has pos[i] = p then at[p] == i
for i in range(n):
    for p in range(n):
        opt.add(Implies(And(meet[i], pos[i] == p), at[p] == i))

# Ensure positions (pos) are unique among met people
for i in range(n):
    for j in range(i+1, n):
        opt.add(Implies(And(meet[i], meet[j]), pos[i] != pos[j]))

# Ensure used positions are contiguous starting at 0:
for p in range(n-1):
    opt.add(Implies(at[p] == -1, at[p+1] == -1))

# Travel-time constraints between consecutive positions
for p in range(n-1):
    # For all pairs (i, j), if they occupy consecutive slots p and p+1,
    # enforce s[j] >= e[i] + travel(loc_i, loc_j)
    disj = []
    for i_idx, (_, loc_i, *_rest_i) in enumerate(people):
        for j_idx, (_, loc_j, *_rest_j) in enumerate(people):
            tt = travel(loc_i, loc_j)
            disj.append(Implies(And(at[p] == i_idx, at[p+1] == j_idx),
                                s[j_idx] >= e[i_idx] + tt))
    if disj:
        opt.add(And(disj))

# Anchor the first meeting to the starting location and time
for i, (_, loc, *_rest) in enumerate(people):
    opt.add(Implies(at[0] == i, s[i] >= day_start + travel(start_location, loc)))

# Objective: maximize number of meetings, then total meeting time
num_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
total_meeting_time = Sum([If(meet[i], e[i] - s[i], 0) for i in range(n)])
opt.maximize(num_meetings)
opt.maximize(total_meeting_time)

# Solve
if opt.check() != sat:
    # Fallback: no feasible meetings
    result = {"itinerary": []}
    print(json.dumps(result))
    exit(0)

m = opt.model()

# Build itinerary by reading positions until -1
itinerary = []
for p in range(n):
    val = m[at[p]].as_long()
    if val == -1:
        break
    i = val
    if is_true(m[meet[i]]):
        name, loc, *_ = people[i]
        start_t = m[s[i]].as_long()
        end_t = m[e[i]].as_long()
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": fmt_time(start_t),
            "end_time": fmt_time(end_t)
        })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))