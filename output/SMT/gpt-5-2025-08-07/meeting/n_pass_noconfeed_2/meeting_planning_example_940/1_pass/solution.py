import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def to_time_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
US = "Union Square"
locations = [
    "Union Square",
    "Mission District",
    "Fisherman's Wharf",
    "Russian Hill",
    "Marina District",
    "North Beach",
    "Chinatown",
    "Pacific Heights",
    "The Castro",
    "Nob Hill",
    "Sunset District",
]

# Directed travel times (minutes)
T = {loc: {} for loc in locations}
def set_t(a,b,v):
    T[a][b] = v

# Populate travel matrix from the problem statement
set_t("Union Square","Mission District",14)
set_t("Union Square","Fisherman's Wharf",15)
set_t("Union Square","Russian Hill",13)
set_t("Union Square","Marina District",18)
set_t("Union Square","North Beach",10)
set_t("Union Square","Chinatown",7)
set_t("Union Square","Pacific Heights",15)
set_t("Union Square","The Castro",17)
set_t("Union Square","Nob Hill",9)
set_t("Union Square","Sunset District",27)

set_t("Mission District","Union Square",15)
set_t("Mission District","Fisherman's Wharf",22)
set_t("Mission District","Russian Hill",15)
set_t("Mission District","Marina District",19)
set_t("Mission District","North Beach",17)
set_t("Mission District","Chinatown",16)
set_t("Mission District","Pacific Heights",16)
set_t("Mission District","The Castro",7)
set_t("Mission District","Nob Hill",12)
set_t("Mission District","Sunset District",24)

set_t("Fisherman's Wharf","Union Square",13)
set_t("Fisherman's Wharf","Mission District",22)
set_t("Fisherman's Wharf","Russian Hill",7)
set_t("Fisherman's Wharf","Marina District",9)
set_t("Fisherman's Wharf","North Beach",6)
set_t("Fisherman's Wharf","Chinatown",12)
set_t("Fisherman's Wharf","Pacific Heights",12)
set_t("Fisherman's Wharf","The Castro",27)
set_t("Fisherman's Wharf","Nob Hill",11)
set_t("Fisherman's Wharf","Sunset District",27)

set_t("Russian Hill","Union Square",10)
set_t("Russian Hill","Mission District",16)
set_t("Russian Hill","Fisherman's Wharf",7)
set_t("Russian Hill","Marina District",7)
set_t("Russian Hill","North Beach",5)
set_t("Russian Hill","Chinatown",9)
set_t("Russian Hill","Pacific Heights",7)
set_t("Russian Hill","The Castro",21)
set_t("Russian Hill","Nob Hill",5)
set_t("Russian Hill","Sunset District",23)

set_t("Marina District","Union Square",16)
set_t("Marina District","Mission District",20)
set_t("Marina District","Fisherman's Wharf",10)
set_t("Marina District","Russian Hill",8)
set_t("Marina District","North Beach",11)
set_t("Marina District","Chinatown",15)
set_t("Marina District","Pacific Heights",7)
set_t("Marina District","The Castro",22)
set_t("Marina District","Nob Hill",12)
set_t("Marina District","Sunset District",19)

set_t("North Beach","Union Square",7)
set_t("North Beach","Mission District",18)
set_t("North Beach","Fisherman's Wharf",5)
set_t("North Beach","Russian Hill",4)
set_t("North Beach","Marina District",9)
set_t("North Beach","Chinatown",6)
set_t("North Beach","Pacific Heights",8)
set_t("North Beach","The Castro",23)
set_t("North Beach","Nob Hill",7)
set_t("North Beach","Sunset District",27)

set_t("Chinatown","Union Square",7)
set_t("Chinatown","Mission District",17)
set_t("Chinatown","Fisherman's Wharf",8)
set_t("Chinatown","Russian Hill",7)
set_t("Chinatown","Marina District",12)
set_t("Chinatown","North Beach",3)
set_t("Chinatown","Pacific Heights",10)
set_t("Chinatown","The Castro",22)
set_t("Chinatown","Nob Hill",9)
set_t("Chinatown","Sunset District",29)

set_t("Pacific Heights","Union Square",12)
set_t("Pacific Heights","Mission District",15)
set_t("Pacific Heights","Fisherman's Wharf",13)
set_t("Pacific Heights","Russian Hill",7)
set_t("Pacific Heights","Marina District",6)
set_t("Pacific Heights","North Beach",9)
set_t("Pacific Heights","Chinatown",11)
set_t("Pacific Heights","The Castro",16)
set_t("Pacific Heights","Nob Hill",8)
set_t("Pacific Heights","Sunset District",21)

set_t("The Castro","Union Square",19)
set_t("The Castro","Mission District",7)
set_t("The Castro","Fisherman's Wharf",24)
set_t("The Castro","Russian Hill",18)
set_t("The Castro","Marina District",21)
set_t("The Castro","North Beach",20)
set_t("The Castro","Chinatown",22)
set_t("The Castro","Pacific Heights",16)
set_t("The Castro","Nob Hill",16)
set_t("The Castro","Sunset District",17)

set_t("Nob Hill","Union Square",7)
set_t("Nob Hill","Mission District",13)
set_t("Nob Hill","Fisherman's Wharf",10)
set_t("Nob Hill","Russian Hill",5)
set_t("Nob Hill","Marina District",11)
set_t("Nob Hill","North Beach",8)
set_t("Nob Hill","Chinatown",6)
set_t("Nob Hill","Pacific Heights",8)
set_t("Nob Hill","The Castro",17)
set_t("Nob Hill","Sunset District",24)

set_t("Sunset District","Union Square",30)
set_t("Sunset District","Mission District",25)
set_t("Sunset District","Fisherman's Wharf",29)
set_t("Sunset District","Russian Hill",24)
set_t("Sunset District","Marina District",21)
set_t("Sunset District","North Beach",28)
set_t("Sunset District","Chinatown",30)
set_t("Sunset District","Pacific Heights",21)
set_t("Sunset District","The Castro",17)
set_t("Sunset District","Nob Hill",27)

# People and their constraints
people = [
    {"name": "Kevin",   "location": "Mission District",     "avail_start": minutes(20,45), "avail_end": minutes(21,45), "min_duration": 60},
    {"name": "Mark",    "location": "Fisherman's Wharf",    "avail_start": minutes(17,15), "avail_end": minutes(20,0),  "min_duration": 90},
    {"name": "Jessica", "location": "Russian Hill",         "avail_start": minutes(9,0),   "avail_end": minutes(15,0),  "min_duration": 120},
    {"name": "Jason",   "location": "Marina District",      "avail_start": minutes(15,15), "avail_end": minutes(21,45), "min_duration": 120},
    {"name": "John",    "location": "North Beach",          "avail_start": minutes(9,45),  "avail_end": minutes(18,0),  "min_duration": 15},
    {"name": "Karen",   "location": "Chinatown",            "avail_start": minutes(16,45), "avail_end": minutes(19,0),  "min_duration": 75},
    {"name": "Sarah",   "location": "Pacific Heights",      "avail_start": minutes(17,30), "avail_end": minutes(18,15), "min_duration": 45},
    {"name": "Amanda",  "location": "The Castro",           "avail_start": minutes(20,0),  "avail_end": minutes(21,15), "min_duration": 60},
    {"name": "Nancy",   "location": "Nob Hill",             "avail_start": minutes(9,45),  "avail_end": minutes(13,0),  "min_duration": 45},
    {"name": "Rebecca", "location": "Sunset District",      "avail_start": minutes(8,45),  "avail_end": minutes(15,0),  "min_duration": 75},
]

arrival_location = US
arrival_time = minutes(9,0)

# Z3 model
opt = Optimize()

# Variables
S = {}  # start times
E = {}  # end times
Sel = {}  # selected for meeting
for p in people:
    name = p["name"]
    S[name] = Int(f"S_{name}")
    E[name] = Int(f"E_{name}")
    Sel[name] = Bool(f"Sel_{name}")
    # Time bounds (whole day)
    opt.add(S[name] >= 0, S[name] <= minutes(23,59))
    opt.add(E[name] >= 0, E[name] <= minutes(23,59))
    # If selected, must satisfy availability and minimum duration
    opt.add(Implies(Sel[name], And(
        S[name] >= p["avail_start"],
        E[name] <= p["avail_end"],
        E[name] - S[name] >= p["min_duration"]
    )))
    # If not selected, allow S,E arbitrary but E >= S for sanity
    opt.add(Implies(Not(Sel[name]), E[name] >= S[name]))
    # Starting from Union Square at 9:00 -> any meeting must start no earlier than travel time from arrival
    # This is a benign lower bound and ensures feasibility of the first hop.
    opt.add(Implies(Sel[name], S[name] >= arrival_time + T[arrival_location][p["location"]]))

# Pairwise non-overlap with travel time between locations
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        ni = pi["name"]
        nj = pj["name"]
        li = pi["location"]
        lj = pj["location"]
        tij = T[li][lj]
        tji = T[lj][li]
        opt.add(Implies(And(Sel[ni], Sel[nj]),
                        Or(S[nj] >= E[ni] + tij,  # i before j
                           S[ni] >= E[nj] + tji)))  # j before i

# Objective: maximize number of friends met, tie-breaker maximize total meeting time
total_meetings = Sum([If(Sel[p["name"]], 1, 0) for p in people])
total_minutes = Sum([If(Sel[p["name"]], E[p["name"]] - S[p["name"]], 0) for p in people])

opt.maximize(total_meetings)
opt.maximize(total_minutes)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    # Extract selected meetings
    itinerary = []
    for p in people:
        name = p["name"]
        if is_true(m[Sel[name]]):
            st = m[S[name]].as_long()
            et = m[E[name]].as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": to_time_str(st),
                "end_time": to_time_str(et)
            })
    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))