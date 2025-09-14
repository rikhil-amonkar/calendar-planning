import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
GGP = "Golden Gate Park"
locations = [
    "Golden Gate Park",
    "Haight-Ashbury",
    "Fisherman's Wharf",
    "The Castro",
    "Chinatown",
    "Alamo Square",
    "North Beach",
    "Russian Hill",
]

# Travel times in minutes (directed)
T = {}
def set_t(a,b,mins):
    T[(a,b)] = mins

# Populate travel times from prompt
set_t("Golden Gate Park","Haight-Ashbury",7)
set_t("Golden Gate Park","Fisherman's Wharf",24)
set_t("Golden Gate Park","The Castro",13)
set_t("Golden Gate Park","Chinatown",23)
set_t("Golden Gate Park","Alamo Square",10)
set_t("Golden Gate Park","North Beach",24)
set_t("Golden Gate Park","Russian Hill",19)

set_t("Haight-Ashbury","Golden Gate Park",7)
set_t("Haight-Ashbury","Fisherman's Wharf",23)
set_t("Haight-Ashbury","The Castro",6)
set_t("Haight-Ashbury","Chinatown",19)
set_t("Haight-Ashbury","Alamo Square",5)
set_t("Haight-Ashbury","North Beach",19)
set_t("Haight-Ashbury","Russian Hill",17)

set_t("Fisherman's Wharf","Golden Gate Park",25)
set_t("Fisherman's Wharf","Haight-Ashbury",22)
set_t("Fisherman's Wharf","The Castro",26)
set_t("Fisherman's Wharf","Chinatown",12)
set_t("Fisherman's Wharf","Alamo Square",20)
set_t("Fisherman's Wharf","North Beach",6)
set_t("Fisherman's Wharf","Russian Hill",7)

set_t("The Castro","Golden Gate Park",11)
set_t("The Castro","Haight-Ashbury",6)
set_t("The Castro","Fisherman's Wharf",24)
set_t("The Castro","Chinatown",20)
set_t("The Castro","Alamo Square",8)
set_t("The Castro","North Beach",20)
set_t("The Castro","Russian Hill",18)

set_t("Chinatown","Golden Gate Park",23)
set_t("Chinatown","Haight-Ashbury",19)
set_t("Chinatown","Fisherman's Wharf",8)
set_t("Chinatown","The Castro",22)
set_t("Chinatown","Alamo Square",17)
set_t("Chinatown","North Beach",3)
set_t("Chinatown","Russian Hill",7)

set_t("Alamo Square","Golden Gate Park",9)
set_t("Alamo Square","Haight-Ashbury",5)
set_t("Alamo Square","Fisherman's Wharf",19)
set_t("Alamo Square","The Castro",8)
set_t("Alamo Square","Chinatown",16)
set_t("Alamo Square","North Beach",15)
set_t("Alamo Square","Russian Hill",13)

set_t("North Beach","Golden Gate Park",22)
set_t("North Beach","Haight-Ashbury",18)
set_t("North Beach","Fisherman's Wharf",5)
set_t("North Beach","The Castro",22)
set_t("North Beach","Chinatown",6)
set_t("North Beach","Alamo Square",16)
set_t("North Beach","Russian Hill",4)

set_t("Russian Hill","Golden Gate Park",21)
set_t("Russian Hill","Haight-Ashbury",17)
set_t("Russian Hill","Fisherman's Wharf",7)
set_t("Russian Hill","The Castro",21)
set_t("Russian Hill","Chinatown",9)
set_t("Russian Hill","Alamo Square",15)
set_t("Russian Hill","North Beach",5)

# Provide zero self travel
for a in locations:
    set_t(a, a, 0)

def travel(a, b):
    return T[(a, b)]

# Origin
origin_loc = GGP
origin_time = minutes(9,0)  # 9:00

# People, locations, time windows, minimum durations
people = [
    {
        "name": "Carol",
        "location": "Haight-Ashbury",
        "window_start": minutes(21,30),
        "window_end": minutes(22,30),
        "min_duration": 60
    },
    {
        "name": "Laura",
        "location": "Fisherman's Wharf",
        "window_start": minutes(11,45),
        "window_end": minutes(21,30),
        "min_duration": 60
    },
    {
        "name": "Karen",
        "location": "The Castro",
        "window_start": minutes(7,15),
        "window_end": minutes(14,0),
        "min_duration": 75
    },
    {
        "name": "Elizabeth",
        "location": "Chinatown",
        "window_start": minutes(12,15),
        "window_end": minutes(21,30),
        "min_duration": 75
    },
    {
        "name": "Deborah",
        "location": "Alamo Square",
        "window_start": minutes(12,0),
        "window_end": minutes(15,0),
        "min_duration": 105
    },
    {
        "name": "Jason",
        "location": "North Beach",
        "window_start": minutes(14,45),
        "window_end": minutes(19,0),
        "min_duration": 90
    },
    {
        "name": "Steven",
        "location": "Russian Hill",
        "window_start": minutes(14,45),
        "window_end": minutes(18,30),
        "min_duration": 120
    },
]

# Z3 model
opt = Optimize()

n = len(people)

start = {}
end = {}
attend = {}
duration = {}

for i, p in enumerate(people):
    start[i] = Int(f"start_{i}")
    end[i] = Int(f"end_{i}")
    attend[i] = Bool(f"attend_{i}")
    duration[i] = IntVal(p["min_duration"])  # fix duration to minimum

    # Bounds
    opt.add(start[i] >= 0, start[i] <= 24*60)
    opt.add(end[i] >= 0, end[i] <= 24*60)

    # If attending, satisfy window and duration; otherwise free within bounds
    opt.add(Implies(attend[i], start[i] >= p["window_start"]))
    opt.add(Implies(attend[i], end[i] <= p["window_end"]))
    opt.add(Implies(attend[i], end[i] == start[i] + duration[i]))

    # Ensure reachability from origin (baseline)
    opt.add(Implies(attend[i], start[i] >= origin_time + travel(origin_loc, p["location"])))

# Disjunctive travel/time constraints between every pair if both attended
for i in range(n):
    for j in range(i+1, n):
        li = people[i]["location"]
        lj = people[j]["location"]
        opt.add(Implies(And(attend[i], attend[j]),
                        Or(start[j] >= end[i] + travel(li, lj),
                           start[i] >= end[j] + travel(lj, li))))


# Objectives:
# 1) Maximize number of meetings
total_meetings = Sum([If(attend[i], 1, 0) for i in range(n)])
opt.maximize(total_meetings)

# 2) Minimize the finish time of the last meeting (makespan)
makespan = Int("makespan")
opt.add(makespan >= 0, makespan <= 24*60)
for i in range(n):
    opt.add(makespan >= If(attend[i], end[i], 0))
opt.minimize(makespan)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    raise SystemExit

m = opt.model()

# Build itinerary
meetings = []
for i, p in enumerate(people):
    if m.evaluate(attend[i], model_completion=True):
        st = m.evaluate(start[i], model_completion=True).as_long()
        en = m.evaluate(end[i], model_completion=True).as_long()
        meetings.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_str(st),
            "end_time": minutes_to_str(en)
        })

# Sort by start time
meetings.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

print(json.dumps({"itinerary": meetings}, ensure_ascii=False))