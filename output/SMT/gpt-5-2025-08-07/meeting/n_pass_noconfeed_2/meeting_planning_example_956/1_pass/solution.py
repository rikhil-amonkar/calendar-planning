import json
from z3 import Optimize, Int, Bool, And, Or, Not, If, Implies, Sum

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "The Castro",
    "Alamo Square",
    "Richmond District",
    "Financial District",
    "Union Square",
    "Fisherman's Wharf",
    "Marina District",
    "Haight-Ashbury",
    "Mission District",
    "Pacific Heights",
    "Golden Gate Park",
]

# Travel times (directed, in minutes)
T = {}
def set_t(a,b,t):
    T.setdefault(a,{})[b]=t
# The Castro to ...
set_t("The Castro","Alamo Square",8)
set_t("The Castro","Richmond District",16)
set_t("The Castro","Financial District",21)
set_t("The Castro","Union Square",19)
set_t("The Castro","Fisherman's Wharf",24)
set_t("The Castro","Marina District",21)
set_t("The Castro","Haight-Ashbury",6)
set_t("The Castro","Mission District",7)
set_t("The Castro","Pacific Heights",16)
set_t("The Castro","Golden Gate Park",11)
# Alamo Square to ...
set_t("Alamo Square","The Castro",8)
set_t("Alamo Square","Richmond District",11)
set_t("Alamo Square","Financial District",17)
set_t("Alamo Square","Union Square",14)
set_t("Alamo Square","Fisherman's Wharf",19)
set_t("Alamo Square","Marina District",15)
set_t("Alamo Square","Haight-Ashbury",5)
set_t("Alamo Square","Mission District",10)
set_t("Alamo Square","Pacific Heights",10)
set_t("Alamo Square","Golden Gate Park",9)
# Richmond District to ...
set_t("Richmond District","The Castro",16)
set_t("Richmond District","Alamo Square",13)
set_t("Richmond District","Financial District",22)
set_t("Richmond District","Union Square",21)
set_t("Richmond District","Fisherman's Wharf",18)
set_t("Richmond District","Marina District",9)
set_t("Richmond District","Haight-Ashbury",10)
set_t("Richmond District","Mission District",20)
set_t("Richmond District","Pacific Heights",10)
set_t("Richmond District","Golden Gate Park",9)
# Financial District to ...
set_t("Financial District","The Castro",20)
set_t("Financial District","Alamo Square",17)
set_t("Financial District","Richmond District",21)
set_t("Financial District","Union Square",9)
set_t("Financial District","Fisherman's Wharf",10)
set_t("Financial District","Marina District",15)
set_t("Financial District","Haight-Ashbury",19)
set_t("Financial District","Mission District",17)
set_t("Financial District","Pacific Heights",13)
set_t("Financial District","Golden Gate Park",23)
# Union Square to ...
set_t("Union Square","The Castro",17)
set_t("Union Square","Alamo Square",15)
set_t("Union Square","Richmond District",20)
set_t("Union Square","Financial District",9)
set_t("Union Square","Fisherman's Wharf",15)
set_t("Union Square","Marina District",18)
set_t("Union Square","Haight-Ashbury",18)
set_t("Union Square","Mission District",14)
set_t("Union Square","Pacific Heights",15)
set_t("Union Square","Golden Gate Park",22)
# Fisherman's Wharf to ...
set_t("Fisherman's Wharf","The Castro",27)
set_t("Fisherman's Wharf","Alamo Square",21)
set_t("Fisherman's Wharf","Richmond District",18)
set_t("Fisherman's Wharf","Financial District",11)
set_t("Fisherman's Wharf","Union Square",13)
set_t("Fisherman's Wharf","Marina District",9)
set_t("Fisherman's Wharf","Haight-Ashbury",22)
set_t("Fisherman's Wharf","Mission District",22)
set_t("Fisherman's Wharf","Pacific Heights",12)
set_t("Fisherman's Wharf","Golden Gate Park",25)
# Marina District to ...
set_t("Marina District","The Castro",22)
set_t("Marina District","Alamo Square",15)
set_t("Marina District","Richmond District",11)
set_t("Marina District","Financial District",17)
set_t("Marina District","Union Square",16)
set_t("Marina District","Fisherman's Wharf",10)
set_t("Marina District","Haight-Ashbury",16)
set_t("Marina District","Mission District",20)
set_t("Marina District","Pacific Heights",7)
set_t("Marina District","Golden Gate Park",18)
# Haight-Ashbury to ...
set_t("Haight-Ashbury","The Castro",6)
set_t("Haight-Ashbury","Alamo Square",5)
set_t("Haight-Ashbury","Richmond District",10)
set_t("Haight-Ashbury","Financial District",21)
set_t("Haight-Ashbury","Union Square",19)
set_t("Haight-Ashbury","Fisherman's Wharf",23)
set_t("Haight-Ashbury","Marina District",17)
set_t("Haight-Ashbury","Mission District",11)
set_t("Haight-Ashbury","Pacific Heights",12)
set_t("Haight-Ashbury","Golden Gate Park",7)
# Mission District to ...
set_t("Mission District","The Castro",7)
set_t("Mission District","Alamo Square",11)
set_t("Mission District","Richmond District",20)
set_t("Mission District","Financial District",15)
set_t("Mission District","Union Square",15)
set_t("Mission District","Fisherman's Wharf",22)
set_t("Mission District","Marina District",19)
set_t("Mission District","Haight-Ashbury",12)
set_t("Mission District","Pacific Heights",16)
set_t("Mission District","Golden Gate Park",17)
# Pacific Heights to ...
set_t("Pacific Heights","The Castro",16)
set_t("Pacific Heights","Alamo Square",10)
set_t("Pacific Heights","Richmond District",12)
set_t("Pacific Heights","Financial District",13)
set_t("Pacific Heights","Union Square",12)
set_t("Pacific Heights","Fisherman's Wharf",13)
set_t("Pacific Heights","Marina District",6)
set_t("Pacific Heights","Haight-Ashbury",11)
set_t("Pacific Heights","Mission District",15)
set_t("Pacific Heights","Golden Gate Park",15)
# Golden Gate Park to ...
set_t("Golden Gate Park","The Castro",13)
set_t("Golden Gate Park","Alamo Square",9)
set_t("Golden Gate Park","Richmond District",7)
set_t("Golden Gate Park","Financial District",26)
set_t("Golden Gate Park","Union Square",22)
set_t("Golden Gate Park","Fisherman's Wharf",24)
set_t("Golden Gate Park","Marina District",16)
set_t("Golden Gate Park","Haight-Ashbury",7)
set_t("Golden Gate Park","Mission District",17)
set_t("Golden Gate Park","Pacific Heights",16)

def travel(a, b):
    return T[a][b]

# Friends and constraints
friends = [
    {"name":"William", "location":"Alamo Square", "start":minutes(15,15), "end":minutes(17,15), "min_dur":60},
    {"name":"Joshua", "location":"Richmond District", "start":minutes(7,0), "end":minutes(20,0), "min_dur":15},
    {"name":"Joseph", "location":"Financial District", "start":minutes(11,15), "end":minutes(13,30), "min_dur":15},
    {"name":"David", "location":"Union Square", "start":minutes(16,45), "end":minutes(19,15), "min_dur":45},
    {"name":"Brian", "location":"Fisherman's Wharf", "start":minutes(13,45), "end":minutes(20,45), "min_dur":105},
    {"name":"Karen", "location":"Marina District", "start":minutes(11,30), "end":minutes(18,30), "min_dur":15},
    {"name":"Anthony", "location":"Haight-Ashbury", "start":minutes(7,15), "end":minutes(10,30), "min_dur":30},
    {"name":"Matthew", "location":"Mission District", "start":minutes(17,15), "end":minutes(19,15), "min_dur":120},
    {"name":"Helen", "location":"Pacific Heights", "start":minutes(8,0), "end":minutes(12,0), "min_dur":75},
    {"name":"Jeffrey", "location":"Golden Gate Park", "start":minutes(19,0), "end":minutes(21,30), "min_dur":60},
]

origin = "The Castro"
arrival_time = minutes(9,0)

n = len(friends)

opt = Optimize()
opt.set(priority='lex')

# Variables
s = [Int(f"s_{i}") for i in range(n)]
e = [Int(f"e_{i}") for i in range(n)]
d = [Int(f"d_{i}") for i in range(n)]
selected = [Bool(f"selected_{i}") for i in range(n)]

for i, fr in enumerate(friends):
    # Basic bounds
    opt.add(s[i] >= 0)
    opt.add(e[i] >= 0)
    opt.add(d[i] >= 0)

    # If selected, must fit window and minimum duration, and end = start + duration
    opt.add(Implies(selected[i], s[i] >= fr["start"]))
    opt.add(Implies(selected[i], e[i] <= fr["end"]))
    opt.add(Implies(selected[i], e[i] == s[i] + d[i]))
    opt.add(Implies(selected[i], d[i] >= fr["min_dur"]))
    opt.add(Implies(selected[i], d[i] <= fr["end"] - fr["start"]))

    # If selected, cannot start before arrival + travel from origin
    opt.add(Implies(selected[i], s[i] >= arrival_time + travel(origin, fr["location"])))

# Pairwise disjunctive precedence with travel times (resource = 1, with travel)
for i in range(n):
    for j in range(i+1, n):
        li = friends[i]["location"]
        lj = friends[j]["location"]
        tij = travel(li, lj)
        tji = travel(lj, li)
        # If both selected, either i then j (with travel), or j then i (with travel)
        opt.add(Implies(And(selected[i], selected[j]),
                        Or(s[j] >= e[i] + tij,
                           s[i] >= e[j] + tji)))

# Objective 1: maximize number of friends met
obj1 = Sum([If(selected[i], 1, 0) for i in range(n)])
opt.maximize(obj1)

# Objective 2: maximize total meeting minutes
obj2 = Sum([d[i] for i in range(n)])
opt.maximize(obj2)

# Solve
if opt.check() != None:
    m = opt.model()
    itinerary = []
    selected_indices = []
    for i in range(n):
        if m.evaluate(selected[i], model_completion=True):
            start_val = m.evaluate(s[i], model_completion=True).as_long()
            end_val = m.evaluate(e[i], model_completion=True).as_long()
            selected_indices.append((start_val, i, end_val))

    # Sort by start time
    selected_indices.sort(key=lambda x: x[0])

    for start_val, i, end_val in selected_indices:
        fr = friends[i]
        itinerary.append({
            "action": "meet",
            "location": fr["location"],
            "person": fr["name"],
            "start_time": fmt_time(start_val),
            "end_time": fmt_time(end_val)
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False, indent=2))
else:
    print(json.dumps({"itinerary": []}, ensure_ascii=False, indent=2))