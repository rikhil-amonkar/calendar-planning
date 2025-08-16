# Solve the SF day meetup optimization with Z3 Optimize:
# - Maximize the number of friends met
# - Respect each friend's availability window
# - Enforce minimum meeting durations
# - Enforce asymmetric travel times between neighborhoods
# - Start at The Castro at 09:00, include travel to the first meeting
# - Enforce travel time between consecutive meetings using disjunctive constraints

from z3 import *
import json

def hm_to_min(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h*60 + m

def min_to_hm(m):
    h = m // 60
    mn = m % 60
    return f"{h:02d}:{mn:02d}"

# Locations
CASTRO = "The Castro"
locs = [
    "The Castro",
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Richmond District",
    "Nob Hill",
    "Marina District",
    "Presidio",
    "Union Square",
    "Financial District",
]

# Travel times (minutes), asymmetric. Fill exactly as provided.
travel = {}

def set_t(a,b,t):
    travel[(a,b)] = t

# The Castro to ...
set_t("The Castro","North Beach",20)
set_t("The Castro","Golden Gate Park",11)
set_t("The Castro","Embarcadero",22)
set_t("The Castro","Haight-Ashbury",6)
set_t("The Castro","Richmond District",16)
set_t("The Castro","Nob Hill",16)
set_t("The Castro","Marina District",21)
set_t("The Castro","Presidio",20)
set_t("The Castro","Union Square",19)
set_t("The Castro","Financial District",21)

# North Beach to ...
set_t("North Beach","The Castro",23)
set_t("North Beach","Golden Gate Park",22)
set_t("North Beach","Embarcadero",6)
set_t("North Beach","Haight-Ashbury",18)
set_t("North Beach","Richmond District",18)
set_t("North Beach","Nob Hill",7)
set_t("North Beach","Marina District",9)
set_t("North Beach","Presidio",17)
set_t("North Beach","Union Square",7)
set_t("North Beach","Financial District",8)

# Golden Gate Park to ...
set_t("Golden Gate Park","The Castro",13)
set_t("Golden Gate Park","North Beach",23)
set_t("Golden Gate Park","Embarcadero",25)
set_t("Golden Gate Park","Haight-Ashbury",7)
set_t("Golden Gate Park","Richmond District",7)
set_t("Golden Gate Park","Nob Hill",20)
set_t("Golden Gate Park","Marina District",16)
set_t("Golden Gate Park","Presidio",11)
set_t("Golden Gate Park","Union Square",22)
set_t("Golden Gate Park","Financial District",26)

# Embarcadero to ...
set_t("Embarcadero","The Castro",25)
set_t("Embarcadero","North Beach",5)
set_t("Embarcadero","Golden Gate Park",25)
set_t("Embarcadero","Haight-Ashbury",21)
set_t("Embarcadero","Richmond District",21)
set_t("Embarcadero","Nob Hill",10)
set_t("Embarcadero","Marina District",12)
set_t("Embarcadero","Presidio",20)
set_t("Embarcadero","Union Square",10)
set_t("Embarcadero","Financial District",5)

# Haight-Ashbury to ...
set_t("Haight-Ashbury","The Castro",6)
set_t("Haight-Ashbury","North Beach",19)
set_t("Haight-Ashbury","Golden Gate Park",7)
set_t("Haight-Ashbury","Embarcadero",20)
set_t("Haight-Ashbury","Richmond District",10)
set_t("Haight-Ashbury","Nob Hill",15)
set_t("Haight-Ashbury","Marina District",17)
set_t("Haight-Ashbury","Presidio",15)
set_t("Haight-Ashbury","Union Square",19)
set_t("Haight-Ashbury","Financial District",21)

# Richmond District to ...
set_t("Richmond District","The Castro",16)
set_t("Richmond District","North Beach",17)
set_t("Richmond District","Golden Gate Park",9)
set_t("Richmond District","Embarcadero",19)
set_t("Richmond District","Haight-Ashbury",10)
set_t("Richmond District","Nob Hill",17)
set_t("Richmond District","Marina District",9)
set_t("Richmond District","Presidio",7)
set_t("Richmond District","Union Square",21)
set_t("Richmond District","Financial District",22)

# Nob Hill to ...
set_t("Nob Hill","The Castro",17)
set_t("Nob Hill","North Beach",8)
set_t("Nob Hill","Golden Gate Park",17)
set_t("Nob Hill","Embarcadero",9)
set_t("Nob Hill","Haight-Ashbury",13)
set_t("Nob Hill","Richmond District",14)
set_t("Nob Hill","Marina District",11)
set_t("Nob Hill","Presidio",17)
set_t("Nob Hill","Union Square",7)
set_t("Nob Hill","Financial District",9)

# Marina District to ...
set_t("Marina District","The Castro",22)
set_t("Marina District","North Beach",11)
set_t("Marina District","Golden Gate Park",18)
set_t("Marina District","Embarcadero",14)
set_t("Marina District","Haight-Ashbury",16)
set_t("Marina District","Richmond District",11)
set_t("Marina District","Nob Hill",12)
set_t("Marina District","Presidio",10)
set_t("Marina District","Union Square",16)
set_t("Marina District","Financial District",17)

# Presidio to ...
set_t("Presidio","The Castro",21)
set_t("Presidio","North Beach",18)
set_t("Presidio","Golden Gate Park",12)
set_t("Presidio","Embarcadero",20)
set_t("Presidio","Haight-Ashbury",15)
set_t("Presidio","Richmond District",7)
set_t("Presidio","Nob Hill",18)
set_t("Presidio","Marina District",11)
set_t("Presidio","Union Square",22)
set_t("Presidio","Financial District",23)

# Union Square to ...
set_t("Union Square","The Castro",17)
set_t("Union Square","North Beach",10)
set_t("Union Square","Golden Gate Park",22)
set_t("Union Square","Embarcadero",11)
set_t("Union Square","Haight-Ashbury",18)
set_t("Union Square","Richmond District",20)
set_t("Union Square","Nob Hill",9)
set_t("Union Square","Marina District",18)
set_t("Union Square","Presidio",24)
set_t("Union Square","Financial District",9)

# Financial District to ...
set_t("Financial District","The Castro",20)
set_t("Financial District","North Beach",7)
set_t("Financial District","Golden Gate Park",23)
set_t("Financial District","Embarcadero",4)
set_t("Financial District","Haight-Ashbury",19)
set_t("Financial District","Richmond District",21)
set_t("Financial District","Nob Hill",8)
set_t("Financial District","Marina District",15)
set_t("Financial District","Presidio",22)
set_t("Financial District","Union Square",9)

# Friends data
friends = {
    "Steven":    {"loc":"North Beach",        "win":("17:30","20:30"), "min_dur":15},
    "Sarah":     {"loc":"Golden Gate Park",   "win":("17:00","19:15"), "min_dur":75},
    "Brian":     {"loc":"Embarcadero",        "win":("14:15","16:00"), "min_dur":105},
    "Stephanie": {"loc":"Haight-Ashbury",     "win":("10:15","12:15"), "min_dur":75},
    "Melissa":   {"loc":"Richmond District",  "win":("14:00","19:30"), "min_dur":30},
    "Nancy":     {"loc":"Nob Hill",           "win":("08:15","12:45"), "min_dur":90},
    "David":     {"loc":"Marina District",    "win":("11:15","13:15"), "min_dur":120},
    "James":     {"loc":"Presidio",           "win":("15:00","18:15"), "min_dur":120},
    "Elizabeth": {"loc":"Union Square",       "win":("11:30","21:00"), "min_dur":60},
    "Robert":    {"loc":"Financial District", "win":("13:15","15:15"), "min_dur":45},
}

# Convert windows to minutes
for p, d in friends.items():
    s, e = d["win"]
    d["ws"] = hm_to_min(s)
    d["we"] = hm_to_min(e)

DAY_START = hm_to_min("09:00")

# Z3 variables
opt = Optimize()

s_vars = {}
e_vars = {}
meet_vars = {}

for p in friends:
    s_vars[p] = Int(f"{p}_start")
    e_vars[p] = Int(f"{p}_end")
    meet_vars[p] = Bool(f"{p}_meet")

    loc = friends[p]["loc"]
    ws = friends[p]["ws"]
    we = friends[p]["we"]
    min_dur = friends[p]["min_dur"]

    # Domain constraints (basic non-negativity and ordering)
    opt.add(s_vars[p] >= 0, e_vars[p] >= 0, e_vars[p] >= s_vars[p])

    # If we meet them, times must be within window and meet duration
    opt.add(Implies(meet_vars[p], And(
        s_vars[p] >= ws,
        e_vars[p] <= we,
        e_vars[p] - s_vars[p] >= min_dur,
        # Must be reachable from the starting point at The Castro at 09:00
        s_vars[p] >= DAY_START + travel[(CASTRO, loc)]
    )))
    # If we don't meet, set zero-length meeting to simplify max/min handling
    opt.add(Implies(Not(meet_vars[p]), e_vars[p] == s_vars[p]))

# Disjunctive no-overlap with travel time between any two met friends
people = list(friends.keys())
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        li = friends[pi]["loc"]
        lj = friends[pj]["loc"]
        tij = travel[(li, lj)]
        tji = travel[(lj, li)]
        opt.add(Implies(And(meet_vars[pi], meet_vars[pj]),
                        Or(e_vars[pi] + tij <= s_vars[pj],
                           e_vars[pj] + tji <= s_vars[pi])))

# Objective 1: maximize number of meetings
meeting_count = Sum([If(meet_vars[p], IntVal(1), IntVal(0)) for p in people])
opt.maximize(meeting_count)

# Objective 2: minimize the day end time (latest end among met friends)
end_day = Int("end_day")
opt.add(end_day >= DAY_START)
for p in people:
    opt.add(Implies(meet_vars[p], end_day >= e_vars[p]))
opt.minimize(end_day)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found")
m = opt.model()

# Extract and sort itinerary
itins = []
for p in people:
    if is_true(m[meet_vars[p]]):
        st = m[s_vars[p]].as_long()
        en = m[e_vars[p]].as_long()
        itins.append({
            "action": "meet",
            "person": p,
            "start_time": min_to_hm(st),
            "end_time": min_to_hm(en),
        })

itins.sort(key=lambda x: x["start_time"])

# Print solution JSON (prefixed by SOLUTION: to match the requested format)
print("SOLUTION:")
print(json.dumps({"itinerary": itins}, ensure_ascii=False))