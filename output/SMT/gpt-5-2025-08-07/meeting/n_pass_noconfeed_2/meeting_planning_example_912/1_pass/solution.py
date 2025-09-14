import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Not, Sum

# Helper time functions
def to_minutes_from_9(t24):
    h, m = map(int, t24.split(":"))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    h = 9 + m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes between locations
T = {}
def add(a, b, v):
    T[(a, b)] = v

# Locations
locations = [
    "Union Square", "Presidio", "Alamo Square", "Marina District", "Financial District",
    "Nob Hill", "Sunset District", "Chinatown", "Russian Hill", "North Beach", "Haight-Ashbury"
]

# Fill travel times as provided
add("Union Square", "Presidio", 24)
add("Union Square", "Alamo Square", 15)
add("Union Square", "Marina District", 18)
add("Union Square", "Financial District", 9)
add("Union Square", "Nob Hill", 9)
add("Union Square", "Sunset District", 27)
add("Union Square", "Chinatown", 7)
add("Union Square", "Russian Hill", 13)
add("Union Square", "North Beach", 10)
add("Union Square", "Haight-Ashbury", 18)

add("Presidio", "Union Square", 22)
add("Presidio", "Alamo Square", 19)
add("Presidio", "Marina District", 11)
add("Presidio", "Financial District", 23)
add("Presidio", "Nob Hill", 18)
add("Presidio", "Sunset District", 15)
add("Presidio", "Chinatown", 21)
add("Presidio", "Russian Hill", 14)
add("Presidio", "North Beach", 18)
add("Presidio", "Haight-Ashbury", 15)

add("Alamo Square", "Union Square", 14)
add("Alamo Square", "Presidio", 17)
add("Alamo Square", "Marina District", 15)
add("Alamo Square", "Financial District", 17)
add("Alamo Square", "Nob Hill", 11)
add("Alamo Square", "Sunset District", 16)
add("Alamo Square", "Chinatown", 15)
add("Alamo Square", "Russian Hill", 13)
add("Alamo Square", "North Beach", 15)
add("Alamo Square", "Haight-Ashbury", 5)

add("Marina District", "Union Square", 16)
add("Marina District", "Presidio", 10)
add("Marina District", "Alamo Square", 15)
add("Marina District", "Financial District", 17)
add("Marina District", "Nob Hill", 12)
add("Marina District", "Sunset District", 19)
add("Marina District", "Chinatown", 15)
add("Marina District", "Russian Hill", 8)
add("Marina District", "North Beach", 11)
add("Marina District", "Haight-Ashbury", 16)

add("Financial District", "Union Square", 9)
add("Financial District", "Presidio", 22)
add("Financial District", "Alamo Square", 17)
add("Financial District", "Marina District", 15)
add("Financial District", "Nob Hill", 8)
add("Financial District", "Sunset District", 30)
add("Financial District", "Chinatown", 5)
add("Financial District", "Russian Hill", 11)
add("Financial District", "North Beach", 7)
add("Financial District", "Haight-Ashbury", 19)

add("Nob Hill", "Union Square", 7)
add("Nob Hill", "Presidio", 17)
add("Nob Hill", "Alamo Square", 11)
add("Nob Hill", "Marina District", 11)
add("Nob Hill", "Financial District", 9)
add("Nob Hill", "Sunset District", 24)
add("Nob Hill", "Chinatown", 6)
add("Nob Hill", "Russian Hill", 5)
add("Nob Hill", "North Beach", 8)
add("Nob Hill", "Haight-Ashbury", 13)

add("Sunset District", "Union Square", 30)
add("Sunset District", "Presidio", 16)
add("Sunset District", "Alamo Square", 17)
add("Sunset District", "Marina District", 21)
add("Sunset District", "Financial District", 30)
add("Sunset District", "Nob Hill", 27)
add("Sunset District", "Chinatown", 30)
add("Sunset District", "Russian Hill", 24)
add("Sunset District", "North Beach", 28)
add("Sunset District", "Haight-Ashbury", 15)

add("Chinatown", "Union Square", 7)
add("Chinatown", "Presidio", 19)
add("Chinatown", "Alamo Square", 17)
add("Chinatown", "Marina District", 12)
add("Chinatown", "Financial District", 5)
add("Chinatown", "Nob Hill", 9)
add("Chinatown", "Sunset District", 29)
add("Chinatown", "Russian Hill", 7)
add("Chinatown", "North Beach", 3)
add("Chinatown", "Haight-Ashbury", 19)

add("Russian Hill", "Union Square", 10)
add("Russian Hill", "Presidio", 14)
add("Russian Hill", "Alamo Square", 15)
add("Russian Hill", "Marina District", 7)
add("Russian Hill", "Financial District", 11)
add("Russian Hill", "Nob Hill", 5)
add("Russian Hill", "Sunset District", 23)
add("Russian Hill", "Chinatown", 9)
add("Russian Hill", "North Beach", 5)
add("Russian Hill", "Haight-Ashbury", 17)

add("North Beach", "Union Square", 7)
add("North Beach", "Presidio", 17)
add("North Beach", "Alamo Square", 16)
add("North Beach", "Marina District", 9)
add("North Beach", "Financial District", 8)
add("North Beach", "Nob Hill", 7)
add("North Beach", "Sunset District", 27)
add("North Beach", "Chinatown", 6)
add("North Beach", "Russian Hill", 4)
add("North Beach", "Haight-Ashbury", 18)

add("Haight-Ashbury", "Union Square", 19)
add("Haight-Ashbury", "Presidio", 15)
add("Haight-Ashbury", "Alamo Square", 5)
add("Haight-Ashbury", "Marina District", 17)
add("Haight-Ashbury", "Financial District", 21)
add("Haight-Ashbury", "Nob Hill", 15)
add("Haight-Ashbury", "Sunset District", 15)
add("Haight-Ashbury", "Chinatown", 19)
add("Haight-Ashbury", "Russian Hill", 17)
add("Haight-Ashbury", "North Beach", 19)

# People constraints
people = {
    "Kimberly": {"location": "Presidio", "window": ("15:30", "16:00"), "min": 15},
    "Elizabeth": {"location": "Alamo Square", "window": ("19:15", "20:15"), "min": 15},
    "Joshua": {"location": "Marina District", "window": ("10:30", "14:15"), "min": 45},
    "Sandra": {"location": "Financial District", "window": ("19:30", "20:15"), "min": 45},
    "Kenneth": {"location": "Nob Hill", "window": ("12:45", "21:45"), "min": 30},
    "Betty": {"location": "Sunset District", "window": ("14:00", "19:00"), "min": 60},
    "Deborah": {"location": "Chinatown", "window": ("17:15", "20:30"), "min": 15},
    "Barbara": {"location": "Russian Hill", "window": ("17:30", "21:15"), "min": 120},
    "Steven": {"location": "North Beach", "window": ("17:45", "20:45"), "min": 90},
    "Daniel": {"location": "Haight-Ashbury", "window": ("18:30", "18:45"), "min": 15},
}

start_location = "Union Square"
day_start = "9:00"
horizon_end = "22:00"  # conservative end of day
HORIZON = to_minutes_from_9(horizon_end)

# Z3 variables
opt = Optimize()
opt.set(priority='lex')

meet = {}
start = {}
dur = {}

for p, info in people.items():
    meet[p] = Bool(f"meet_{p}")
    start[p] = Int(f"start_{p}")  # minutes from 9:00
    dur[p] = Int(f"dur_{p}")
    w_start = to_minutes_from_9(info["window"][0])
    w_end = to_minutes_from_9(info["window"][1])
    min_d = info["min"]
    # Domains
    opt.add(start[p] >= 0, start[p] <= HORIZON)
    opt.add(dur[p] >= 0, dur[p] <= HORIZON)
    # If meet, must fit within window and meet minimum
    opt.add(Implies(meet[p], And(
        start[p] >= w_start,
        start[p] + dur[p] <= w_end,
        dur[p] >= min_d,
        start[p] + dur[p] <= HORIZON,
        start[p] >= T[(start_location, info["location"])]  # can reach from day start
    )))
    # If not meeting, duration is zero
    opt.add(Implies(Not(meet[p]), dur[p] == 0))

# Travel feasibility between any pair of meetings
names = list(people.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        p = names[i]
        q = names[j]
        lp = people[p]["location"]
        lq = people[q]["location"]
        tpq = T[(lp, lq)]
        tqp = T[(lq, lp)]
        # If both meetings occur, they must not overlap and include travel time
        opt.add(Implies(And(meet[p], meet[q]),
                        Or(start[p] >= start[q] + dur[q] + tqp,
                           start[q] >= start[p] + dur[p] + tpq)))

# Objectives
count_meetings = Sum([If(meet[p], 1, 0) for p in people])
total_minutes = Sum([If(meet[p], dur[p], 0) for p in people])

opt.maximize(count_meetings)
opt.maximize(total_minutes)

if opt.check() != None:
    model = opt.model()
    itinerary = []
    for p in people:
        if model.evaluate(meet[p], model_completion=True):
            s = model.evaluate(start[p]).as_long()
            d = model.evaluate(dur[p]).as_long()
            e = s + d
            itinerary.append({
                "person": p,
                "location": people[p]["location"],
                "start": s,
                "end": e
            })
    # Sort by start time
    itinerary.sort(key=lambda x: x["start"])
    # Convert times to H:MM
    output = {"itinerary": []}
    for item in itinerary:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_time(item["start"]),
            "end_time": minutes_to_time(item["end"])
        })
    print(json.dumps(output))
else:
    print(json.dumps({"itinerary": []}))