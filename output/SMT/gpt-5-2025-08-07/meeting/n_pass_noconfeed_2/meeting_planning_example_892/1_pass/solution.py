import json
from z3 import *

def mins_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Time constants
DAY_START = 9 * 60  # 9:00 = 540
DAY_END = 21 * 60 + 30  # 21:30 = 1290 (latest any availability ends)

# Locations
locations = [
    "Marina District",
    "Bayview",
    "Sunset District",
    "Richmond District",
    "Nob Hill",
    "Chinatown",
    "Haight-Ashbury",
    "North Beach",
    "Russian Hill",
    "Embarcadero",
]

# Travel time matrix (minutes)
t = {}
def add(a,b,m):
    t[(a,b)] = m

add("Marina District","Bayview",27)
add("Marina District","Sunset District",19)
add("Marina District","Richmond District",11)
add("Marina District","Nob Hill",12)
add("Marina District","Chinatown",15)
add("Marina District","Haight-Ashbury",16)
add("Marina District","North Beach",11)
add("Marina District","Russian Hill",8)
add("Marina District","Embarcadero",14)

add("Bayview","Marina District",27)
add("Bayview","Sunset District",23)
add("Bayview","Richmond District",25)
add("Bayview","Nob Hill",20)
add("Bayview","Chinatown",19)
add("Bayview","Haight-Ashbury",19)
add("Bayview","North Beach",22)
add("Bayview","Russian Hill",23)
add("Bayview","Embarcadero",19)

add("Sunset District","Marina District",21)
add("Sunset District","Bayview",22)
add("Sunset District","Richmond District",12)
add("Sunset District","Nob Hill",27)
add("Sunset District","Chinatown",30)
add("Sunset District","Haight-Ashbury",15)
add("Sunset District","North Beach",28)
add("Sunset District","Russian Hill",24)
add("Sunset District","Embarcadero",30)

add("Richmond District","Marina District",9)
add("Richmond District","Bayview",27)
add("Richmond District","Sunset District",11)
add("Richmond District","Nob Hill",17)
add("Richmond District","Chinatown",20)
add("Richmond District","Haight-Ashbury",10)
add("Richmond District","North Beach",17)
add("Richmond District","Russian Hill",13)
add("Richmond District","Embarcadero",19)

add("Nob Hill","Marina District",11)
add("Nob Hill","Bayview",19)
add("Nob Hill","Sunset District",24)
add("Nob Hill","Richmond District",14)
add("Nob Hill","Chinatown",6)
add("Nob Hill","Haight-Ashbury",13)
add("Nob Hill","North Beach",8)
add("Nob Hill","Russian Hill",5)
add("Nob Hill","Embarcadero",9)

add("Chinatown","Marina District",12)
add("Chinatown","Bayview",20)
add("Chinatown","Sunset District",29)
add("Chinatown","Richmond District",20)
add("Chinatown","Nob Hill",9)
add("Chinatown","Haight-Ashbury",19)
add("Chinatown","North Beach",3)
add("Chinatown","Russian Hill",7)
add("Chinatown","Embarcadero",5)

add("Haight-Ashbury","Marina District",17)
add("Haight-Ashbury","Bayview",18)
add("Haight-Ashbury","Sunset District",15)
add("Haight-Ashbury","Richmond District",10)
add("Haight-Ashbury","Nob Hill",15)
add("Haight-Ashbury","Chinatown",19)
add("Haight-Ashbury","North Beach",19)
add("Haight-Ashbury","Russian Hill",17)
add("Haight-Ashbury","Embarcadero",20)

add("North Beach","Marina District",9)
add("North Beach","Bayview",25)
add("North Beach","Sunset District",27)
add("North Beach","Richmond District",18)
add("North Beach","Nob Hill",7)
add("North Beach","Chinatown",6)
add("North Beach","Haight-Ashbury",18)
add("North Beach","Russian Hill",4)
add("North Beach","Embarcadero",6)

add("Russian Hill","Marina District",7)
add("Russian Hill","Bayview",23)
add("Russian Hill","Sunset District",23)
add("Russian Hill","Richmond District",14)
add("Russian Hill","Nob Hill",5)
add("Russian Hill","Chinatown",9)
add("Russian Hill","Haight-Ashbury",17)
add("Russian Hill","North Beach",5)
add("Russian Hill","Embarcadero",8)

add("Embarcadero","Marina District",12)
add("Embarcadero","Bayview",21)
add("Embarcadero","Sunset District",30)
add("Embarcadero","Richmond District",21)
add("Embarcadero","Nob Hill",10)
add("Embarcadero","Chinatown",7)
add("Embarcadero","Haight-Ashbury",21)
add("Embarcadero","North Beach",5)
add("Embarcadero","Russian Hill",8)

# People, locations, availability windows, minimum meeting durations (in minutes)
def time_to_min(h, m): return h*60+m

people = [
    {"name":"Charles","location":"Bayview","avail_start":time_to_min(11,30),"avail_end":time_to_min(14,30),"min_dur":45},
    {"name":"Robert","location":"Sunset District","avail_start":time_to_min(16,45),"avail_end":time_to_min(21,0),"min_dur":30},
    {"name":"Karen","location":"Richmond District","avail_start":time_to_min(19,15),"avail_end":time_to_min(21,30),"min_dur":60},
    {"name":"Rebecca","location":"Nob Hill","avail_start":time_to_min(16,15),"avail_end":time_to_min(20,30),"min_dur":90},
    {"name":"Margaret","location":"Chinatown","avail_start":time_to_min(14,15),"avail_end":time_to_min(19,45),"min_dur":120},
    {"name":"Patricia","location":"Haight-Ashbury","avail_start":time_to_min(14,30),"avail_end":time_to_min(20,30),"min_dur":45},
    {"name":"Mark","location":"North Beach","avail_start":time_to_min(14,0),"avail_end":time_to_min(18,30),"min_dur":105},
    {"name":"Melissa","location":"Russian Hill","avail_start":time_to_min(13,0),"avail_end":time_to_min(19,45),"min_dur":30},
    {"name":"Laura","location":"Embarcadero","avail_start":time_to_min(7,45),"avail_end":time_to_min(13,15),"min_dur":105},
]

origin = "Marina District"

opt = Optimize()

# Variables per person
vars_data = {}
for p in people:
    name = p["name"]
    s = Int(f"s_{name}")  # start time in minutes
    e = Int(f"e_{name}")  # end time in minutes
    m = Bool(f"m_{name}") # meet or not
    vars_data[name] = {"s":s,"e":e,"m":m}

    # Domain bounds
    opt.add(s >= 0, s <= 24*60)
    opt.add(e >= 0, e <= 24*60)

    # If meeting them, respect availability, minimum duration, and reachable from start
    start_travel = t[(origin, p["location"])]
    opt.add(Implies(m, And(
        s >= p["avail_start"],
        e <= p["avail_end"],
        e > s,
        e - s >= p["min_dur"],
        s >= DAY_START + start_travel,
        e <= DAY_END
    )))
    # If not meeting, times are zero (to avoid unconstrained values)
    opt.add(Implies(Not(m), And(s == 0, e == 0)))

# Pairwise non-overlap with travel: impose ordering when both are met
order_bools = {}
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        bi = vars_data[pi["name"]]
        bj = vars_data[pj["name"]]
        b = Bool(f"before_{pi['name']}_{pj['name']}")
        order_bools[(pi["name"], pj["name"])] = b
        tij = t[(pi["location"], pj["location"])]
        tji = t[(pj["location"], pi["location"])]
        opt.add(Implies(And(bi["m"], bj["m"]),
                        Or(And(b, bj["s"] >= bi["e"] + tij),
                           And(Not(b), bi["s"] >= bj["e"] + tji))
                        ))

# Objectives: maximize number of people met, then maximize total meeting time
count_met = Sum([If(vars_data[p["name"]]["m"], 1, 0) for p in people])
total_meet_time = Sum([If(vars_data[p["name"]]["m"], vars_data[p["name"]]["e"] - vars_data[p["name"]]["s"], 0) for p in people])

opt.maximize(count_met)
opt.maximize(total_meet_time)

if opt.check() != sat:
    # Should not happen, but output empty itinerary if unsat
    result = {"itinerary": []}
    print(json.dumps(result))
else:
    model = opt.model()
    schedule = []
    for p in people:
        name = p["name"]
        vd = vars_data[name]
        if is_true(model.evaluate(vd["m"])):
            s_val = model.evaluate(vd["s"]).as_long()
            e_val = model.evaluate(vd["e"]).as_long()
            schedule.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": mins_to_time(s_val),
                "end_time": mins_to_time(e_val)
            })
    # Sort by start time
    schedule.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))
    print(json.dumps({"itinerary": schedule}, ensure_ascii=False))