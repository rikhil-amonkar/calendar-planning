import json
from z3 import *

def minutes_since_9am(hhmm):
    hh, mm = map(int, hhmm.split(":"))
    return (hh - 9) * 60 + mm

def time_from_minutes(m):
    total_minutes = 9 * 60 + m
    h = total_minutes // 60
    mn = total_minutes % 60
    return f"{h:02d}:{mn:02d}"

# Build travel time matrix (minutes)
travel = {}
def add(a, b, t):
    travel.setdefault(a, {})[b] = t

# Distances (directed) as provided
add("Bayview","North Beach",22)
add("Bayview","Fisherman's Wharf",25)
add("Bayview","Haight-Ashbury",19)
add("Bayview","Nob Hill",20)
add("Bayview","Golden Gate Park",22)
add("Bayview","Union Square",18)
add("Bayview","Alamo Square",16)
add("Bayview","Presidio",32)
add("Bayview","Chinatown",19)
add("Bayview","Pacific Heights",23)

add("North Beach","Bayview",25)
add("North Beach","Fisherman's Wharf",5)
add("North Beach","Haight-Ashbury",18)
add("North Beach","Nob Hill",7)
add("North Beach","Golden Gate Park",22)
add("North Beach","Union Square",7)
add("North Beach","Alamo Square",16)
add("North Beach","Presidio",17)
add("North Beach","Chinatown",6)
add("North Beach","Pacific Heights",8)

add("Fisherman's Wharf","Bayview",26)
add("Fisherman's Wharf","North Beach",6)
add("Fisherman's Wharf","Haight-Ashbury",22)
add("Fisherman's Wharf","Nob Hill",11)
add("Fisherman's Wharf","Golden Gate Park",25)
add("Fisherman's Wharf","Union Square",13)
add("Fisherman's Wharf","Alamo Square",21)
add("Fisherman's Wharf","Presidio",17)
add("Fisherman's Wharf","Chinatown",12)
add("Fisherman's Wharf","Pacific Heights",12)

add("Haight-Ashbury","Bayview",18)
add("Haight-Ashbury","North Beach",19)
add("Haight-Ashbury","Fisherman's Wharf",23)
add("Haight-Ashbury","Nob Hill",15)
add("Haight-Ashbury","Golden Gate Park",7)
add("Haight-Ashbury","Union Square",19)
add("Haight-Ashbury","Alamo Square",5)
add("Haight-Ashbury","Presidio",15)
add("Haight-Ashbury","Chinatown",19)
add("Haight-Ashbury","Pacific Heights",12)

add("Nob Hill","Bayview",19)
add("Nob Hill","North Beach",8)
add("Nob Hill","Fisherman's Wharf",10)
add("Nob Hill","Haight-Ashbury",13)
add("Nob Hill","Golden Gate Park",17)
add("Nob Hill","Union Square",7)
add("Nob Hill","Alamo Square",11)
add("Nob Hill","Presidio",17)
add("Nob Hill","Chinatown",6)
add("Nob Hill","Pacific Heights",8)

add("Golden Gate Park","Bayview",23)
add("Golden Gate Park","North Beach",23)
add("Golden Gate Park","Fisherman's Wharf",24)
add("Golden Gate Park","Haight-Ashbury",7)
add("Golden Gate Park","Nob Hill",20)
add("Golden Gate Park","Union Square",22)
add("Golden Gate Park","Alamo Square",9)
add("Golden Gate Park","Presidio",11)
add("Golden Gate Park","Chinatown",23)
add("Golden Gate Park","Pacific Heights",16)

add("Union Square","Bayview",15)
add("Union Square","North Beach",10)
add("Union Square","Fisherman's Wharf",15)
add("Union Square","Haight-Ashbury",18)
add("Union Square","Nob Hill",9)
add("Union Square","Golden Gate Park",22)
add("Union Square","Alamo Square",15)
add("Union Square","Presidio",24)
add("Union Square","Chinatown",7)
add("Union Square","Pacific Heights",15)

add("Alamo Square","Bayview",16)
add("Alamo Square","North Beach",15)
add("Alamo Square","Fisherman's Wharf",19)
add("Alamo Square","Haight-Ashbury",5)
add("Alamo Square","Nob Hill",11)
add("Alamo Square","Golden Gate Park",9)
add("Alamo Square","Union Square",14)
add("Alamo Square","Presidio",17)
add("Alamo Square","Chinatown",15)
add("Alamo Square","Pacific Heights",10)

add("Presidio","Bayview",31)
add("Presidio","North Beach",18)
add("Presidio","Fisherman's Wharf",19)
add("Presidio","Haight-Ashbury",15)
add("Presidio","Nob Hill",18)
add("Presidio","Golden Gate Park",12)
add("Presidio","Union Square",22)
add("Presidio","Alamo Square",19)
add("Presidio","Chinatown",21)
add("Presidio","Pacific Heights",11)

add("Chinatown","Bayview",20)
add("Chinatown","North Beach",3)
add("Chinatown","Fisherman's Wharf",8)
add("Chinatown","Haight-Ashbury",19)
add("Chinatown","Nob Hill",9)
add("Chinatown","Golden Gate Park",23)
add("Chinatown","Union Square",7)
add("Chinatown","Alamo Square",17)
add("Chinatown","Presidio",19)
add("Chinatown","Pacific Heights",10)

add("Pacific Heights","Bayview",22)
add("Pacific Heights","North Beach",9)
add("Pacific Heights","Fisherman's Wharf",13)
add("Pacific Heights","Haight-Ashbury",11)
add("Pacific Heights","Nob Hill",8)
add("Pacific Heights","Golden Gate Park",15)
add("Pacific Heights","Union Square",12)
add("Pacific Heights","Alamo Square",10)
add("Pacific Heights","Presidio",11)
add("Pacific Heights","Chinatown",11)

# People, locations, availability windows, and minimum meeting durations
people = {
    "Brian":      {"loc": "North Beach",       "start": minutes_since_9am("13:00"), "end": minutes_since_9am("19:00"), "min": 90},
    "Richard":    {"loc": "Fisherman's Wharf", "start": minutes_since_9am("11:00"), "end": minutes_since_9am("12:45"), "min": 60},
    "Ashley":     {"loc": "Haight-Ashbury",    "start": minutes_since_9am("15:00"), "end": minutes_since_9am("20:30"), "min": 90},
    "Elizabeth":  {"loc": "Nob Hill",          "start": minutes_since_9am("11:45"), "end": minutes_since_9am("18:30"), "min": 75},
    "Jessica":    {"loc": "Golden Gate Park",  "start": minutes_since_9am("20:00"), "end": minutes_since_9am("21:45"), "min": 105},
    "Deborah":    {"loc": "Union Square",      "start": minutes_since_9am("17:30"), "end": minutes_since_9am("22:00"), "min": 60},
    "Kimberly":   {"loc": "Alamo Square",      "start": minutes_since_9am("17:30"), "end": minutes_since_9am("21:15"), "min": 45},
    "Matthew":    {"loc": "Presidio",          "start": minutes_since_9am("08:15"), "end": minutes_since_9am("09:00"), "min": 15},
    "Kenneth":    {"loc": "Chinatown",         "start": minutes_since_9am("13:45"), "end": minutes_since_9am("19:30"), "min": 105},
    "Anthony":    {"loc": "Pacific Heights",   "start": minutes_since_9am("14:15"), "end": minutes_since_9am("16:00"), "min": 30},
}

# Z3 variables
meet_vars = {}
start_vars = {}
end_vars = {}

opt = Optimize()
opt.set(priority='lex')

for p, info in people.items():
    meet = Bool(f"meet_{p}")
    s = Int(f"start_{p}")
    e = Int(f"end_{p}")
    meet_vars[p] = meet
    start_vars[p] = s
    end_vars[p] = e
    # Domain bounds (non-negative times from 9:00 onward)
    opt.add(s >= 0, e >= 0)
    # If met, respect availability window and minimum duration
    opt.add(Implies(meet, s >= info["start"]))
    opt.add(Implies(meet, e <= info["end"]))
    opt.add(Implies(meet, e - s >= info["min"]))
    # Reachability from starting point (Bayview at 9:00)
    loc = info["loc"]
    if "Bayview" in travel and loc in travel["Bayview"]:
        opt.add(Implies(meet, s >= travel["Bayview"][loc]))

# Pairwise non-overlap with travel times between meetings
names = list(people.keys())
for i in range(len(names)):
    for j in range(i+1, len(names)):
        p = names[i]
        q = names[j]
        lp = people[p]["loc"]
        lq = people[q]["loc"]
        # If both are met, one must precede the other with travel time
        before_pq = Bool(f"before_{p}_{q}")
        # Only enforce when both meetings happen
        if lp in travel and lq in travel[lp] and lq in travel and lp in travel[lq]:
            tpq = travel[lp][lq]
            tqp = travel[lq][lp]
        else:
            # If some travel time missing, assume large to discourage/avoid
            tpq = 10**6
            tqp = 10**6
        opt.add(Implies(And(meet_vars[p], meet_vars[q], before_pq),
                        end_vars[p] + tpq <= start_vars[q]))
        opt.add(Implies(And(meet_vars[p], meet_vars[q], Not(before_pq)),
                        end_vars[q] + tqp <= start_vars[p]))

# Objectives:
# 1) Maximize number of people met
total_met = Sum([If(meet_vars[p], 1, 0) for p in people])
opt.maximize(total_met)
# 2) Maximize total meeting time (lexicographic secondary)
total_meeting_time = Sum([If(meet_vars[p], end_vars[p] - start_vars[p], 0) for p in people])
opt.maximize(total_meeting_time)

# Solve
if opt.check() != sat:
    # No feasible schedule
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    meetings = []
    for p in people:
        if is_true(model.eval(meet_vars[p])):
            s = model.eval(start_vars[p]).as_long()
            e = model.eval(end_vars[p]).as_long()
            meetings.append({
                "person": p,
                "start": s,
                "end": e
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start"])
    itinerary = []
    for m in meetings:
        itinerary.append({
            "action": "meet",
            "person": m["person"],
            "start_time": time_from_minutes(m["start"]),
            "end_time": time_from_minutes(m["end"])
        })
    print("SOLUTION:" + json.dumps({"itinerary": itinerary}))