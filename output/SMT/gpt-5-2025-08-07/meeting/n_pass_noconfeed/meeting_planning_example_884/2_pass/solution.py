import json
from z3 import Int, Bool, Optimize, Sum, If, And, Or, Not, Implies, sat, is_true

def parse_time(tstr):
    # Example inputs: "9:00AM", "5:30PM", "13:15" (24h optional)
    tstr = tstr.strip().upper()
    ampm = None
    if tstr.endswith("AM"):
        ampm = "AM"
        tstr = tstr[:-2]
    elif tstr.endswith("PM"):
        ampm = "PM"
        tstr = tstr[:-2]
    tstr = tstr.strip()
    parts = tstr.split(":")
    h = int(parts[0])
    m = int(parts[1]) if len(parts) > 1 else 0
    if ampm == "AM":
        if h == 12:
            h = 0
    elif ampm == "PM":
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Richmond District",
    "Chinatown",
    "Sunset District",
    "Alamo Square",
    "Financial District",
    "North Beach",
    "Embarcadero",
    "Presidio",
    "Golden Gate Park",
    "Bayview",
]

# Travel times (minutes) as given
travel = {}
def set_travel(a, b, t):
    travel[(a, b)] = t

set_travel("Richmond District", "Chinatown", 20)
set_travel("Richmond District", "Sunset District", 11)
set_travel("Richmond District", "Alamo Square", 13)
set_travel("Richmond District", "Financial District", 22)
set_travel("Richmond District", "North Beach", 17)
set_travel("Richmond District", "Embarcadero", 19)
set_travel("Richmond District", "Presidio", 7)
set_travel("Richmond District", "Golden Gate Park", 9)
set_travel("Richmond District", "Bayview", 27)

set_travel("Chinatown", "Richmond District", 20)
set_travel("Chinatown", "Sunset District", 29)
set_travel("Chinatown", "Alamo Square", 17)
set_travel("Chinatown", "Financial District", 5)
set_travel("Chinatown", "North Beach", 3)
set_travel("Chinatown", "Embarcadero", 5)
set_travel("Chinatown", "Presidio", 19)
set_travel("Chinatown", "Golden Gate Park", 23)
set_travel("Chinatown", "Bayview", 20)

set_travel("Sunset District", "Richmond District", 12)
set_travel("Sunset District", "Chinatown", 30)
set_travel("Sunset District", "Alamo Square", 17)
set_travel("Sunset District", "Financial District", 30)
set_travel("Sunset District", "North Beach", 28)
set_travel("Sunset District", "Embarcadero", 30)
set_travel("Sunset District", "Presidio", 16)
set_travel("Sunset District", "Golden Gate Park", 11)
set_travel("Sunset District", "Bayview", 22)

set_travel("Alamo Square", "Richmond District", 11)
set_travel("Alamo Square", "Chinatown", 15)
set_travel("Alamo Square", "Sunset District", 16)
set_travel("Alamo Square", "Financial District", 17)
set_travel("Alamo Square", "North Beach", 15)
set_travel("Alamo Square", "Embarcadero", 16)
set_travel("Alamo Square", "Presidio", 17)
set_travel("Alamo Square", "Golden Gate Park", 9)
set_travel("Alamo Square", "Bayview", 16)

set_travel("Financial District", "Richmond District", 21)
set_travel("Financial District", "Chinatown", 5)
set_travel("Financial District", "Sunset District", 30)
set_travel("Financial District", "Alamo Square", 17)
set_travel("Financial District", "North Beach", 7)
set_travel("Financial District", "Embarcadero", 4)
set_travel("Financial District", "Presidio", 22)
set_travel("Financial District", "Golden Gate Park", 23)
set_travel("Financial District", "Bayview", 19)

set_travel("North Beach", "Richmond District", 18)
set_travel("North Beach", "Chinatown", 6)
set_travel("North Beach", "Sunset District", 27)
set_travel("North Beach", "Alamo Square", 16)
set_travel("North Beach", "Financial District", 8)
set_travel("North Beach", "Embarcadero", 6)
set_travel("North Beach", "Presidio", 17)
set_travel("North Beach", "Golden Gate Park", 22)
set_travel("North Beach", "Bayview", 25)

set_travel("Embarcadero", "Richmond District", 21)
set_travel("Embarcadero", "Chinatown", 7)
set_travel("Embarcadero", "Sunset District", 30)
set_travel("Embarcadero", "Alamo Square", 19)
set_travel("Embarcadero", "Financial District", 5)
set_travel("Embarcadero", "North Beach", 5)
set_travel("Embarcadero", "Presidio", 20)
set_travel("Embarcadero", "Golden Gate Park", 25)
set_travel("Embarcadero", "Bayview", 21)

set_travel("Presidio", "Richmond District", 7)
set_travel("Presidio", "Chinatown", 21)
set_travel("Presidio", "Sunset District", 15)
set_travel("Presidio", "Alamo Square", 19)
set_travel("Presidio", "Financial District", 23)
set_travel("Presidio", "North Beach", 18)
set_travel("Presidio", "Embarcadero", 20)
set_travel("Presidio", "Golden Gate Park", 12)
set_travel("Presidio", "Bayview", 31)

set_travel("Golden Gate Park", "Richmond District", 7)
set_travel("Golden Gate Park", "Chinatown", 23)
set_travel("Golden Gate Park", "Sunset District", 10)
set_travel("Golden Gate Park", "Alamo Square", 9)
set_travel("Golden Gate Park", "Financial District", 26)
set_travel("Golden Gate Park", "North Beach", 23)
set_travel("Golden Gate Park", "Embarcadero", 25)
set_travel("Golden Gate Park", "Presidio", 11)
set_travel("Golden Gate Park", "Bayview", 23)

set_travel("Bayview", "Richmond District", 25)
set_travel("Bayview", "Chinatown", 19)
set_travel("Bayview", "Sunset District", 23)
set_travel("Bayview", "Alamo Square", 16)
set_travel("Bayview", "Financial District", 19)
set_travel("Bayview", "North Beach", 22)
set_travel("Bayview", "Embarcadero", 19)
set_travel("Bayview", "Presidio", 32)
set_travel("Bayview", "Golden Gate Park", 22)

def get_travel(a, b):
    return travel[(a, b)]

# People and constraints
people = [
    {"name": "Robert",  "location": "Chinatown",          "avail_start": "7:45AM", "avail_end": "5:30PM", "min_meet": 120},
    {"name": "David",   "location": "Sunset District",    "avail_start": "12:30PM", "avail_end": "7:45PM", "min_meet": 45},
    {"name": "Matthew", "location": "Alamo Square",       "avail_start": "8:45AM", "avail_end": "1:45PM", "min_meet": 90},
    {"name": "Jessica", "location": "Financial District", "avail_start": "9:30AM", "avail_end": "6:45PM", "min_meet": 45},
    {"name": "Melissa", "location": "North Beach",        "avail_start": "7:15AM", "avail_end": "4:45PM", "min_meet": 45},
    {"name": "Mark",    "location": "Embarcadero",        "avail_start": "3:15PM", "avail_end": "5:00PM", "min_meet": 45},
    {"name": "Deborah", "location": "Presidio",           "avail_start": "7:00PM", "avail_end": "7:45PM", "min_meet": 45},
    {"name": "Karen",   "location": "Golden Gate Park",   "avail_start": "7:30PM", "avail_end": "10:00PM","min_meet": 120},
    {"name": "Laura",   "location": "Bayview",            "avail_start": "9:15PM", "avail_end": "10:15PM","min_meet": 15},
]

origin_location = "Richmond District"
origin_time = parse_time("9:00AM")

# Convert availability to minutes
for p in people:
    p["avail_start_min"] = parse_time(p["avail_start"])
    p["avail_end_min"] = parse_time(p["avail_end"])

n = len(people)
idx = {people[i]["name"]: i for i in range(n)}

# Z3 variables
opt = Optimize()
opt.set(priority='lex')

visited = [Bool(f"visited_{i}") for i in range(n)]
first = [Bool(f"first_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
end = [Int(f"end_{i}") for i in range(n)]
dur = [Int(f"dur_{i}") for i in range(n)]

# Precedence booleans for all ordered pairs i != j
precedence = {}
for i in range(n):
    for j in range(n):
        if i != j:
            precedence[(i, j)] = Bool(f"before_{i}_{j}")

# Per-person availability and meeting constraints
for i, p in enumerate(people):
    smin = p["avail_start_min"]
    emin = p["avail_end_min"]
    min_d = p["min_meet"]

    # If visited, enforce times within availability and duration constraints
    opt.add(Implies(visited[i], And(
        start[i] >= smin,
        end[i] <= emin,
        dur[i] >= min_d,
        end[i] == start[i] + dur[i]
    )))
    # If not visited, set times to 0 for cleanliness
    opt.add(Implies(Not(visited[i]), And(
        start[i] == 0,
        end[i] == 0,
        dur[i] == 0
    )))
    # First implies visited
    opt.add(Implies(first[i], visited[i]))
    # If first, start no earlier than arrival from origin
    origin_to_loc = get_travel(origin_location, p["location"])
    opt.add(Implies(first[i], start[i] >= origin_time + origin_to_loc))

# Precedence/order constraints
for i in range(n):
    for j in range(i + 1, n):
        pij = precedence[(i, j)]
        pji = precedence[(j, i)]
        # If both visited, exactly one precedence holds
        opt.add(Implies(And(visited[i], visited[j]), pij != pji))
        # If at least one not visited, no precedence
        opt.add(Implies(Not(And(visited[i], visited[j])), And(Not(pij), Not(pji))))

        # Timing with travel
        ti = get_travel(people[i]["location"], people[j]["location"])
        tj = get_travel(people[j]["location"], people[i]["location"])
        opt.add(Implies(pij, end[i] + ti <= start[j]))
        opt.add(Implies(pji, end[j] + tj <= start[i]))

# First node properties: no one precedes the first
for i in range(n):
    opt.add(Implies(first[i], And([Not(precedence[(j, i)]) for j in range(n) if j != i])))

# Every visited person must be either first or have a predecessor
for i in range(n):
    preds = [precedence[(j, i)] for j in range(n) if j != i]
    opt.add(Implies(visited[i], Or(first[i], Or(preds) if preds else False)))

# Exactly one first if any are visited
sum_visited = Sum([If(visited[i], 1, 0) for i in range(n)])
sum_first = Sum([If(first[i], 1, 0) for i in range(n)])
opt.add(Or(sum_visited == 0, sum_first == 1))

# Objectives: maximize number of friends met, then total meeting duration
total_meetings = sum_visited
total_duration = Sum([If(visited[i], dur[i], 0) for i in range(n)])
opt.maximize(total_meetings)
opt.maximize(total_duration)

# Solve
if opt.check() != sat:
    # Fallback in rare unsat case: output empty itinerary JSON
    print(json.dumps({"itinerary": []}, indent=2))
else:
    m = opt.model()
    schedule = []
    for i, p in enumerate(people):
        if is_true(m.eval(visited[i], model_completion=True)):
            s = m.eval(start[i], model_completion=True).as_long()
            e = m.eval(end[i], model_completion=True).as_long()
            schedule.append({
                "person": p["name"],
                "location": p["location"],
                "start": s,
                "end": e
            })
    # Sort by start times
    schedule.sort(key=lambda x: x["start"])

    itinerary = []
    for item in schedule:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start"]),
            "end_time": fmt_time(item["end"])
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))