import json
from z3 import Optimize, Int, And, Or, If, Sum, Implies

def time_to_min(s):
    s = s.strip().upper()
    if s.endswith("AM"):
        ampm = "AM"
    elif s.endswith("PM"):
        ampm = "PM"
    else:
        raise ValueError("Time must end with AM or PM")
    s_time = s[:-2]
    h, m = map(int, s_time.split(":"))
    if h == 12:
        h = 0
    total = h * 60 + m
    if ampm == "PM":
        total += 12 * 60
    return total

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Locations
locations = [
    "Mission District",
    "Alamo Square",
    "Presidio",
    "Russian Hill",
    "North Beach",
    "Golden Gate Park",
    "Richmond District",
    "Embarcadero",
    "Financial District",
    "Marina District",
]

# Travel times (minutes) as per problem statement
travel = {loc: {} for loc in locations}

# Fill in the travel times exactly as provided
# Mission District to ...
travel["Mission District"]["Alamo Square"] = 11
travel["Mission District"]["Presidio"] = 25
travel["Mission District"]["Russian Hill"] = 15
travel["Mission District"]["North Beach"] = 17
travel["Mission District"]["Golden Gate Park"] = 17
travel["Mission District"]["Richmond District"] = 20
travel["Mission District"]["Embarcadero"] = 19
travel["Mission District"]["Financial District"] = 15
travel["Mission District"]["Marina District"] = 19

# Alamo Square to ...
travel["Alamo Square"]["Mission District"] = 10
travel["Alamo Square"]["Presidio"] = 17
travel["Alamo Square"]["Russian Hill"] = 13
travel["Alamo Square"]["North Beach"] = 15
travel["Alamo Square"]["Golden Gate Park"] = 9
travel["Alamo Square"]["Richmond District"] = 11
travel["Alamo Square"]["Embarcadero"] = 16
travel["Alamo Square"]["Financial District"] = 17
travel["Alamo Square"]["Marina District"] = 15

# Presidio to ...
travel["Presidio"]["Mission District"] = 26
travel["Presidio"]["Alamo Square"] = 19
travel["Presidio"]["Russian Hill"] = 14
travel["Presidio"]["North Beach"] = 18
travel["Presidio"]["Golden Gate Park"] = 12
travel["Presidio"]["Richmond District"] = 7
travel["Presidio"]["Embarcadero"] = 20
travel["Presidio"]["Financial District"] = 23
travel["Presidio"]["Marina District"] = 11

# Russian Hill to ...
travel["Russian Hill"]["Mission District"] = 16
travel["Russian Hill"]["Alamo Square"] = 15
travel["Russian Hill"]["Presidio"] = 14
travel["Russian Hill"]["North Beach"] = 5
travel["Russian Hill"]["Golden Gate Park"] = 21
travel["Russian Hill"]["Richmond District"] = 14
travel["Russian Hill"]["Embarcadero"] = 8
travel["Russian Hill"]["Financial District"] = 11
travel["Russian Hill"]["Marina District"] = 7

# North Beach to ...
travel["North Beach"]["Mission District"] = 18
travel["North Beach"]["Alamo Square"] = 16
travel["North Beach"]["Presidio"] = 17
travel["North Beach"]["Russian Hill"] = 4
travel["North Beach"]["Golden Gate Park"] = 22
travel["North Beach"]["Richmond District"] = 18
travel["North Beach"]["Embarcadero"] = 6
travel["North Beach"]["Financial District"] = 8
travel["North Beach"]["Marina District"] = 9

# Golden Gate Park to ...
travel["Golden Gate Park"]["Mission District"] = 17
travel["Golden Gate Park"]["Alamo Square"] = 9
travel["Golden Gate Park"]["Presidio"] = 11
travel["Golden Gate Park"]["Russian Hill"] = 19
travel["Golden Gate Park"]["North Beach"] = 23
travel["Golden Gate Park"]["Richmond District"] = 7
travel["Golden Gate Park"]["Embarcadero"] = 25
travel["Golden Gate Park"]["Financial District"] = 26
travel["Golden Gate Park"]["Marina District"] = 16

# Richmond District to ...
travel["Richmond District"]["Mission District"] = 20
travel["Richmond District"]["Alamo Square"] = 13
travel["Richmond District"]["Presidio"] = 7
travel["Richmond District"]["Russian Hill"] = 13
travel["Richmond District"]["North Beach"] = 17
travel["Richmond District"]["Golden Gate Park"] = 9
travel["Richmond District"]["Embarcadero"] = 19
travel["Richmond District"]["Financial District"] = 22
travel["Richmond District"]["Marina District"] = 9

# Embarcadero to ...
travel["Embarcadero"]["Mission District"] = 20
travel["Embarcadero"]["Alamo Square"] = 19
travel["Embarcadero"]["Presidio"] = 20
travel["Embarcadero"]["Russian Hill"] = 8
travel["Embarcadero"]["North Beach"] = 5
travel["Embarcadero"]["Golden Gate Park"] = 25
travel["Embarcadero"]["Richmond District"] = 21
travel["Embarcadero"]["Financial District"] = 5
travel["Embarcadero"]["Marina District"] = 12

# Financial District to ...
travel["Financial District"]["Mission District"] = 17
travel["Financial District"]["Alamo Square"] = 17
travel["Financial District"]["Presidio"] = 22
travel["Financial District"]["Russian Hill"] = 11
travel["Financial District"]["North Beach"] = 7
travel["Financial District"]["Golden Gate Park"] = 23
travel["Financial District"]["Richmond District"] = 21
travel["Financial District"]["Embarcadero"] = 4
travel["Financial District"]["Marina District"] = 15

# Marina District to ...
travel["Marina District"]["Mission District"] = 20
travel["Marina District"]["Alamo Square"] = 15
travel["Marina District"]["Presidio"] = 10
travel["Marina District"]["Russian Hill"] = 8
travel["Marina District"]["North Beach"] = 11
travel["Marina District"]["Golden Gate Park"] = 18
travel["Marina District"]["Richmond District"] = 11
travel["Marina District"]["Embarcadero"] = 14
travel["Marina District"]["Financial District"] = 17

# People: name, location, availability start, availability end, minimum duration
people = [
    ("Laura", "Alamo Square", "2:30PM", "4:15PM", 75),
    ("Brian", "Presidio", "10:15AM", "5:00PM", 30),
    ("Karen", "Russian Hill", "6:00PM", "8:15PM", 90),
    ("Stephanie", "North Beach", "10:15AM", "4:00PM", 75),
    ("Helen", "Golden Gate Park", "11:30AM", "9:45PM", 120),
    ("Sandra", "Richmond District", "8:00AM", "3:15PM", 30),
    ("Mary", "Embarcadero", "4:45PM", "6:45PM", 120),
    ("Deborah", "Financial District", "7:00PM", "8:45PM", 105),
    ("Elizabeth", "Marina District", "8:30AM", "1:15PM", 105),
]

# Convert to index-based arrays
n = len(people)
names = [p[0] for p in people]
locs = [p[1] for p in people]
avail_start = [time_to_min(p[2]) for p in people]
avail_end = [time_to_min(p[3]) for p in people]
min_dur = [p[4] for p in people]

# Sanity: ensure travel dictionary contains all needed pairs
for l in locations:
    if l not in travel:
        travel[l] = {}
for a in locations:
    for b in locations:
        if a == b:
            if b not in travel[a]:
                travel[a][b] = 0
        else:
            if b not in travel[a]:
                raise RuntimeError(f"Missing travel time from {a} to {b}")

# Model with ordered slots
S = n  # maximum number of meetings possible
opt = Optimize()
opt.set(priority='lex')

pid = [Int(f"pid_{k}") for k in range(S)]  # -1 means empty, else index 0..n-1
start = [Int(f"start_{k}") for k in range(S)]
end = [Int(f"end_{k}") for k in range(S)]
dur = [Int(f"dur_{k}") for k in range(S)]

# Domain and basic constraints
for k in range(S):
    # Domain for pid
    opt.add(Or(pid[k] == -1, And(pid[k] >= 0, pid[k] < n)))
    # Time bounds
    opt.add(start[k] >= 0, end[k] >= 0, dur[k] >= 0)
    opt.add(start[k] <= 24 * 60, end[k] <= 24 * 60)

# Contiguity of non-empty slots: once empty, all following are empty
for k in range(1, S):
    opt.add(Implies(pid[k-1] == -1, pid[k] == -1))

# No duplicate persons across slots
for i in range(S):
    for j in range(i+1, S):
        opt.add(Or(pid[i] == -1, pid[j] == -1, pid[i] != pid[j]))

# Slot-specific constraints: availability and duration
for k in range(S):
    # If empty, zero times; else align with a specific person's availability and minimum duration
    cases = []
    for i in range(n):
        cases.append(And(
            pid[k] == i,
            end[k] == start[k] + dur[k],
            start[k] >= avail_start[i],
            end[k] <= avail_end[i],
            dur[k] >= min_dur[i]
        ))
    opt.add(If(pid[k] == -1,
               And(start[k] == 0, end[k] == 0, dur[k] == 0),
               Or(cases)))

# Travel/time continuity
# Start of day: at Mission District at 9:00AM
start_of_day_loc = "Mission District"
start_of_day_time = time_to_min("9:00AM")

if S > 0:
    first_cases = []
    for i in range(n):
        first_cases.append(And(
            pid[0] == i,
            start[0] >= start_of_day_time + travel[start_of_day_loc][locs[i]]
        ))
    opt.add(Or(pid[0] == -1, Or(first_cases)))

for k in range(1, S):
    # If both slots are non-empty, enforce travel time between them
    pair_cases = []
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            pair_cases.append(And(
                pid[k-1] == i,
                pid[k] == j,
                start[k] >= end[k-1] + travel[locs[i]][locs[j]]
            ))
    opt.add(Or(pid[k] == -1, pid[k-1] == -1, Or(pair_cases)))

# Objective: maximize number of meetings, then total meeting time
meet_count = Sum([If(pid[k] == -1, 0, 1) for k in range(S)])
total_minutes = Sum(dur)
opt.maximize(meet_count)
opt.maximize(total_minutes)

# Solve
if opt.check() != None and opt.check().r == 1:
    model = opt.model()
    itinerary = []
    for k in range(S):
        pid_val = model[pid[k]].as_long()
        if pid_val >= 0:
            name = names[pid_val]
            loc = locs[pid_val]
            st = model[start[k]].as_long()
            en = model[end[k]].as_long()
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": min_to_time(st),
                "end_time": min_to_time(en)
            })
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, ensure_ascii=False))