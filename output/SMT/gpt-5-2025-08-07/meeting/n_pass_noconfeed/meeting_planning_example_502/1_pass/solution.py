import json
from z3 import Optimize, Int, Bool, If, Sum, And, Or, Not, Implies, sat

# Helper functions
def to_minutes(tstr):
    # Expects strings like "11:00AM" or "3:30PM"
    tstr = tstr.strip().upper()
    if tstr.endswith("AM") or tstr.endswith("PM"):
        ampm = tstr[-2:]
        hhmm = tstr[:-2]
    else:
        hhmm = tstr
        ampm = None
    hh, mm = hhmm.split(":")
    h = int(hh)
    m = int(mm)
    if ampm == "AM":
        if h == 12:
            h = 0
    elif ampm == "PM":
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Data setup
locations = [
    "Financial District",
    "Golden Gate Park",
    "Chinatown",
    "Union Square",
    "Fisherman's Wharf",
    "Pacific Heights",
    "North Beach",
]

# Directed travel times (minutes)
T = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7,
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24,
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3,
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10,
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6,
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9,
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8,
    },
}

# People and constraints
people = [
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "avail_start": to_minutes("11:00AM"),
        "avail_end": to_minutes("3:00PM"),
        "min_dur": 105,
    },
    {
        "name": "Karen",
        "location": "Chinatown",
        "avail_start": to_minutes("1:45PM"),
        "avail_end": to_minutes("4:30PM"),
        "min_dur": 15,
    },
    {
        "name": "Brian",
        "location": "Union Square",
        "avail_start": to_minutes("3:00PM"),
        "avail_end": to_minutes("5:15PM"),
        "min_dur": 30,
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "avail_start": to_minutes("8:00AM"),
        "avail_end": to_minutes("11:15AM"),
        "min_dur": 30,
    },
    {
        "name": "Joseph",
        "location": "Pacific Heights",
        "avail_start": to_minutes("8:15AM"),
        "avail_end": to_minutes("9:30AM"),
        "min_dur": 60,
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "avail_start": to_minutes("2:30PM"),
        "avail_end": to_minutes("8:45PM"),
        "min_dur": 120,
    },
]

# Start conditions
start_location = "Financial District"
start_time = to_minutes("9:00AM")

# Build Z3 model
opt = Optimize()

n = len(people)
meet = [Bool(f"meet_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]
dur = [people[i]["min_dur"] for i in range(n)]

# Bounds on times
for i in range(n):
    opt.add(start[i] >= 0, start[i] <= 24 * 60)

# Availability constraints
for i in range(n):
    a = people[i]
    s = start[i]
    d = dur[i]
    opt.add(
        Implies(
            meet[i],
            And(
                s >= a["avail_start"],
                s + d <= a["avail_end"],
            ),
        )
    )

# Precedence variables for all unordered pairs (i<j): before[i,j] means i before j
before = {}
for i in range(n):
    for j in range(i + 1, n):
        before[(i, j)] = Bool(f"before_{i}_{j}")

def i_before_j(i, j):
    if i == j:
        raise ValueError("i_before_j called with identical indices")
    if i < j:
        return before[(i, j)]
    else:
        return Not(before[(j, i)])

# Non-overlap and travel-time constraints between any two meetings
for i in range(n):
    for j in range(i + 1, n):
        li = people[i]["location"]
        lj = people[j]["location"]
        tij = T[li][lj]
        tji = T[lj][li]
        si = start[i]
        sj = start[j]
        di = dur[i]
        dj = dur[j]

        opt.add(
            Implies(
                And(meet[i], meet[j]),
                Or(
                    And(before[(i, j)], sj >= si + di + tij),
                    And(Not(before[(i, j)]), si >= sj + dj + tji),
                ),
            )
        )

# Ensure the schedule is connected to the starting point at 9:00 in Financial District
# For any meeting that doesn't have someone before it, it must respect the initial travel time.
for i in range(n):
    li = people[i]["location"]
    travel_from_start = T[start_location][li]
    predecessors = []
    for j in range(n):
        if j == i:
            continue
        predecessors.append(And(meet[j], i_before_j(j, i)))
    # If we meet person i, either they have a real predecessor, or they must start after traveling from the start.
    if predecessors:
        opt.add(
            Implies(
                meet[i],
                Or(
                    start[i] >= start_time + travel_from_start,
                    Or(predecessors),
                ),
            )
        )
    else:
        # Only one person case (not applicable here but for completeness)
        opt.add(Implies(meet[i], start[i] >= start_time + travel_from_start))

# Objective: maximize number of people met
total_met = Sum([If(meet[i], 1, 0) for i in range(n)])
h1 = opt.maximize(total_met)

# Small tie-breaker: minimize the finishing time (latest end time), to get a compact plan if same count
latest_end = Int("latest_end")
opt.add(latest_end >= 0, latest_end <= 24 * 60)
for i in range(n):
    opt.add(Implies(meet[i], latest_end >= start[i] + dur[i]))
h2 = opt.minimize(latest_end)

# Solve
if opt.check() != sat:
    result = {"itinerary": []}
else:
    m = opt.model()
    plan = []
    for i in range(n):
        if m.evaluate(meet[i], model_completion=True):
            smin = m.evaluate(start[i], model_completion=True).as_long()
            emin = smin + dur[i]
            plan.append({
                "person": people[i]["name"],
                "location": people[i]["location"],
                "start": smin,
                "end": emin
            })
    # Sort by start time
    plan.sort(key=lambda x: x["start"])
    itinerary = []
    for p in plan:
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["person"],
            "start_time": minutes_to_str(p["start"]),
            "end_time": minutes_to_str(p["end"]),
        })
    result = {"itinerary": itinerary}

print(json.dumps(result, ensure_ascii=False))