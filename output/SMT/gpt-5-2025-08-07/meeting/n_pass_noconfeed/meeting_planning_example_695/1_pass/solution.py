# SOLUTION:
# This script uses the Z3 SMT solver to compute an optimal meeting schedule
# that maximizes the number of friends met while respecting travel times and availability windows.
from z3 import *
import json

def parse_time_12h(s):
    s = s.strip().upper()
    # Expect formats like "4:15PM", "9:00AM", "11:45AM", "10:00PM"
    if s.endswith("AM"):
        ampm = "AM"
        time_part = s[:-2]
    elif s.endswith("PM"):
        ampm = "PM"
        time_part = s[:-2]
    else:
        raise ValueError(f"Invalid time: {s}")
    time_part = time_part.strip()
    h_str, m_str = time_part.split(":")
    h = int(h_str)
    m = int(m_str)
    if ampm == "AM":
        if h == 12:
            h = 0
    else:  # PM
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "Bayview",
    "Nob Hill",
    "Union Square",
    "Chinatown",
    "The Castro",
    "Presidio",
    "Pacific Heights",
    "Russian Hill",
]

# Directed travel times in minutes (as provided)
travel = {
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "The Castro"): 20,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 19,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Chinatown", "Bayview"): 22,
    ("Chinatown", "Nob Hill"): 8,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Russian Hill"): 7,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Chinatown"): 20,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Russian Hill"): 14,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Union Square"): 11,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Pacific Heights"): 7,
}

def t(from_loc, to_loc):
    return travel[(from_loc, to_loc)]

# Starting point and time
start_location = "Bayview"
start_time = parse_time_12h("9:00AM")

# People, locations, availability, and minimum durations
people = {
    "Paul": {
        "location": "Nob Hill",
        "avail_start": parse_time_12h("4:15PM"),
        "avail_end": parse_time_12h("9:15PM"),
        "min_duration": 60,
    },
    "Carol": {
        "location": "Union Square",
        "avail_start": parse_time_12h("6:00PM"),
        "avail_end": parse_time_12h("8:15PM"),
        "min_duration": 120,
    },
    "Patricia": {
        "location": "Chinatown",
        "avail_start": parse_time_12h("8:00PM"),
        "avail_end": parse_time_12h("9:30PM"),
        "min_duration": 75,
    },
    "Karen": {
        "location": "The Castro",
        "avail_start": parse_time_12h("5:00PM"),
        "avail_end": parse_time_12h("7:00PM"),
        "min_duration": 45,
    },
    "Nancy": {
        "location": "Presidio",
        "avail_start": parse_time_12h("11:45AM"),
        "avail_end": parse_time_12h("10:00PM"),
        "min_duration": 30,
    },
    "Jeffrey": {
        "location": "Pacific Heights",
        "avail_start": parse_time_12h("8:00PM"),
        "avail_end": parse_time_12h("8:45PM"),
        "min_duration": 45,
    },
    "Matthew": {
        "location": "Russian Hill",
        "avail_start": parse_time_12h("3:45PM"),
        "avail_end": parse_time_12h("9:45PM"),
        "min_duration": 75,
    },
}

names = list(people.keys())

# Z3 variables
s = {name: Int(f"s_{name}") for name in names}
e = {name: Int(f"e_{name}") for name in names}
meet = {name: Bool(f"meet_{name}") for name in names}

# Before relationship booleans
before = {}
for i in names:
    before[i] = {}
    for j in names:
        if i == j:
            continue
        before[i][j] = Bool(f"before_{i}_{j}")

o = Optimize()

# Time domains and availability constraints
for name in names:
    ps = people[name]
    o.add(s[name] >= ps["avail_start"])
    o.add(e[name] <= ps["avail_end"])
    o.add(e[name] >= s[name])
    # Meeting implies within window and min duration
    o.add(Implies(meet[name], And(s[name] >= ps["avail_start"],
                                  e[name] <= ps["avail_end"],
                                  e[name] - s[name] >= ps["min_duration"])))
    # If not meeting, keep times within window (already bounded by above)

# Pairwise ordering and travel feasibility
for i in names:
    for j in names:
        if i == j:
            continue
        # before(i,j) implies both are met and timing with travel
        o.add(Implies(before[i][j], And(meet[i], meet[j], e[i] + t(people[i]["location"], people[j]["location"]) <= s[j])))
        # If both are met, one must be before the other
        o.add(Implies(And(meet[i], meet[j]), Or(before[i][j], before[j][i])))
        # Cannot be both ways
        o.add(Not(And(before[i][j], before[j][i])))

# Reachability from Bayview: each met meeting either is reachable directly from start, or has a predecessor
for j in names:
    preds = []
    for i in names:
        if i == j:
            continue
        preds.append(before[i][j])
    # If meeting j, then it's either first from Bayview, or has some predecessor i
    o.add(Implies(meet[j], Or(s[j] >= start_time + t(start_location, people[j]["location"]), Or(preds) if preds else False)))

# Objective: maximize number of meetings, then maximize total meeting time
total_met = Sum([If(meet[name], 1, 0) for name in names])
total_duration = Sum([If(meet[name], e[name] - s[name], 0) for name in names])
o.maximize(total_met)
o.maximize(total_duration)

res = o.check()
if res != sat and res != unknown:
    print(json.dumps({"itinerary": []}, indent=2))
else:
    m = o.model()
    itinerary = []
    for name in names:
        if is_true(m.evaluate(meet[name])):
            start_min = m.evaluate(s[name]).as_long()
            end_min = m.evaluate(e[name]).as_long()
            itinerary.append({
                "action": "meet",
                "location": people[name]["location"],
                "person": name,
                "start_time": minutes_to_str(start_min),
                "end_time": minutes_to_str(end_min),
            })
    # Sort by start_time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))
    print(json.dumps({"itinerary": itinerary}, indent=2))