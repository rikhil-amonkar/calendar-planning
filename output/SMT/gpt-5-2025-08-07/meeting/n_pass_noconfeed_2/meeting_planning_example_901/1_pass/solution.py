import json
from z3 import Int, Bool, Optimize, If, And, Or, Sum, sat

def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Minutes for key times
MIN = {
    "7:30": 7*60+30,
    "8:00": 8*60,
    "8:30": 8*60+30,
    "9:00": 9*60,
    "9:15": 9*60+15,
    "10:30": 10*60+30,
    "11:30": 11*60+30,
    "13:45": 13*60+45,
    "14:45": 14*60+45,
    "15:15": 15*60+15,
    "18:15": 18*60+15,
    "18:45": 18*60+45,
    "19:15": 19*60+15,
    "21:15": 21*60+15,
    "17:30": 17*60+30,
    "20:30": 20*60+30,
}

START_LOCATION = "Russian Hill"
ARRIVE_TIME = MIN["9:00"]

# Directed travel time in minutes between neighborhoods
T = {}
def add(a,b,t):
    T[(a,b)] = t

# Populate travel times
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

# People and constraints
people = [
    # name, location, avail_start, avail_end, min_minutes
    ("Emily", "Pacific Heights", MIN["9:15"], MIN["13:45"], 120),
    ("Helen", "North Beach", MIN["13:45"], MIN["18:45"], 30),
    ("Kimberly", "Golden Gate Park", MIN["18:45"], MIN["21:15"], 75),
    ("James", "Embarcadero", MIN["10:30"], MIN["11:30"], 30),
    ("Linda", "Haight-Ashbury", MIN["7:30"], MIN["19:15"], 15),
    ("Paul", "Fisherman's Wharf", MIN["14:45"], MIN["18:45"], 90),
    ("Anthony", "Mission District", MIN["8:00"], MIN["14:45"], 105),
    ("Nancy", "Alamo Square", MIN["8:30"], MIN["13:45"], 120),
    ("William", "Bayview", MIN["17:30"], MIN["20:30"], 120),
    ("Margaret", "Richmond District", MIN["15:15"], MIN["18:15"], 45),
]

idx = {p[0]: i for i,p in enumerate(people)}
loc_of = {p[0]: p[1] for p in people}
avail = {p[0]: (p[2], p[3]) for p in people}
min_dur = {p[0]: p[4] for p in people}

n = len(people)

opt = Optimize()

meet = [Bool(f"meet_{i}") for i in range(n)]
s = [Int(f"s_{i}") for i in range(n)]
e = [Int(f"e_{i}") for i in range(n)]

# Bounds on times
for i in range(n):
    opt.add(s[i] >= 0, s[i] <= 24*60)
    opt.add(e[i] >= 0, e[i] <= 24*60)
    opt.add(e[i] >= s[i])
    # If not meeting, collapse interval
    opt.add(Or(meet[i] == False, And(s[i] >= avail[people[i][0]][0], e[i] <= avail[people[i][0]][1], e[i] - s[i] >= min_dur[people[i][0]])))
    opt.add(Or(meet[i] == True, e[i] == s[i]))

# Pairwise non-overlap with travel feasibility
for i in range(n):
    for j in range(i+1, n):
        li = people[i][1]
        lj = people[j][1]
        tij = T[(li, lj)]
        tji = T[(lj, li)]
        opt.add(
            Or(
                meet[i] == False,
                meet[j] == False,
                e[i] + tij <= s[j],  # i before j
                e[j] + tji <= s[i],  # j before i
            )
        )

# Origin anchoring or predecessor travel feasibility for each meeting
anchors = []
for i in range(n):
    li = people[i][1]
    origin_travel = T[(START_LOCATION, li)]
    pred_options = []
    for j in range(n):
        if i == j:
            continue
        lj = people[j][1]
        pred_options.append(And(meet[j], e[j] + T[(lj, li)] <= s[i]))
    # Either anchored to origin or has some predecessor that can reach in time
    opt.add(
        Or(
            meet[i] == False,
            s[i] >= ARRIVE_TIME + origin_travel,
            Or(pred_options) if pred_options else False
        )
    )
    anchors.append(And(meet[i], s[i] >= ARRIVE_TIME + origin_travel))

# Ensure at least one scheduled meeting (optional). We'll allow zero to be feasible but objective will avoid it.
# Also ensure that if there is at least one meeting, at least one is anchored from origin.
total_meet = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.add(Or(total_meet == 0, Or(anchors)))

# Objectives: maximize number of people met, then maximize total minutes
total_minutes = Sum([If(meet[i], e[i] - s[i], 0) for i in range(n)])
opt.maximize(total_meet)
opt.maximize(total_minutes)

res = opt.check()
itinerary = []
if res == sat:
    m = opt.model()
    entries = []
    for i in range(n):
        if m.evaluate(meet[i]).is_true():
            si = m.evaluate(s[i]).as_long()
            ei = m.evaluate(e[i]).as_long()
            person = people[i][0]
            loc = people[i][1]
            entries.append({
                "person": person,
                "location": loc,
                "start": si,
                "end": ei
            })
    # Sort by start time
    entries.sort(key=lambda x: x["start"])
    for ent in entries:
        itinerary.append({
            "action": "meet",
            "location": ent["location"],
            "person": ent["person"],
            "start_time": fmt_time(ent["start"]),
            "end_time": fmt_time(ent["end"])
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))