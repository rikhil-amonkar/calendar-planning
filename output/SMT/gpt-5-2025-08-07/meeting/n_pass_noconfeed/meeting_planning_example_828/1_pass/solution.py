import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Marina District",
    "Richmond District",
    "Union Square",
    "Nob Hill",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Embarcadero",
    "Financial District",
    "North Beach",
    "Presidio",
]

# Travel times (in minutes), directional
T = {
    "Marina District": {
        "Richmond District": 11,
        "Union Square": 16,
        "Nob Hill": 12,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Financial District": 17,
        "North Beach": 11,
        "Presidio": 10,
        "Marina District": 0,
    },
    "Richmond District": {
        "Marina District": 9,
        "Union Square": 21,
        "Nob Hill": 17,
        "Fisherman's Wharf": 18,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Financial District": 22,
        "North Beach": 17,
        "Presidio": 7,
        "Richmond District": 0,
    },
    "Union Square": {
        "Marina District": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Fisherman's Wharf": 15,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Financial District": 9,
        "North Beach": 10,
        "Presidio": 24,
        "Union Square": 0,
    },
    "Nob Hill": {
        "Marina District": 11,
        "Richmond District": 14,
        "Union Square": 7,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Financial District": 9,
        "North Beach": 8,
        "Presidio": 17,
        "Nob Hill": 0,
    },
    "Fisherman's Wharf": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Financial District": 11,
        "North Beach": 6,
        "Presidio": 17,
        "Fisherman's Wharf": 0,
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 20,
        "Fisherman's Wharf": 24,
        "Embarcadero": 25,
        "Financial District": 26,
        "North Beach": 23,
        "Presidio": 11,
        "Golden Gate Park": 0,
    },
    "Embarcadero": {
        "Marina District": 12,
        "Richmond District": 21,
        "Union Square": 10,
        "Nob Hill": 10,
        "Fisherman's Wharf": 6,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20,
        "Embarcadero": 0,
    },
    "Financial District": {
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Nob Hill": 8,
        "Fisherman's Wharf": 10,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "North Beach": 7,
        "Presidio": 22,
        "Financial District": 0,
    },
    "North Beach": {
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 7,
        "Nob Hill": 7,
        "Fisherman's Wharf": 5,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Financial District": 8,
        "Presidio": 17,
        "North Beach": 0,
    },
    "Presidio": {
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Financial District": 23,
        "North Beach": 18,
        "Presidio": 0,
    },
}

# People and their constraints
people = [
    {
        "name": "Stephanie",
        "location": "Richmond District",
        "avail_start": minutes(16, 15),
        "avail_end": minutes(21, 30),
        "min_duration": 75,
    },
    {
        "name": "William",
        "location": "Union Square",
        "avail_start": minutes(10, 45),
        "avail_end": minutes(17, 30),
        "min_duration": 45,
    },
    {
        "name": "Elizabeth",
        "location": "Nob Hill",
        "avail_start": minutes(12, 15),
        "avail_end": minutes(15, 0),
        "min_duration": 105,
    },
    {
        "name": "Joseph",
        "location": "Fisherman's Wharf",
        "avail_start": minutes(12, 45),
        "avail_end": minutes(14, 0),
        "min_duration": 75,
    },
    {
        "name": "Anthony",
        "location": "Golden Gate Park",
        "avail_start": minutes(13, 0),
        "avail_end": minutes(20, 30),
        "min_duration": 75,
    },
    {
        "name": "Barbara",
        "location": "Embarcadero",
        "avail_start": minutes(19, 15),
        "avail_end": minutes(20, 30),
        "min_duration": 75,
    },
    {
        "name": "Carol",
        "location": "Financial District",
        "avail_start": minutes(11, 45),
        "avail_end": minutes(16, 15),
        "min_duration": 60,
    },
    {
        "name": "Sandra",
        "location": "North Beach",
        "avail_start": minutes(10, 0),
        "avail_end": minutes(12, 30),
        "min_duration": 15,
    },
    {
        "name": "Kenneth",
        "location": "Presidio",
        "avail_start": minutes(21, 15),
        "avail_end": minutes(22, 15),
        "min_duration": 45,
    },
]

start_location = "Marina District"
start_time = minutes(9, 0)
day_end = minutes(24, 0)

opt = Optimize()

# Decision variables
starts = {}
ends = {}
selects = {}
durations = {}

for p in people:
    name = p["name"]
    starts[name] = Int(f"start_{name}")
    ends[name] = Int(f"end_{name}")
    selects[name] = Bool(f"select_{name}")
    durations[name] = Int(f"dur_{name}")
    # Domain
    opt.add(starts[name] >= 0, starts[name] <= day_end)
    opt.add(ends[name] >= 0, ends[name] <= day_end)
    opt.add(durations[name] >= 0)
    opt.add(durations[name] == ends[name] - starts[name])
    # Availability and minimum duration if selected
    opt.add(Implies(selects[name], starts[name] >= p["avail_start"]))
    opt.add(Implies(selects[name], ends[name] <= p["avail_end"]))
    opt.add(Implies(selects[name], durations[name] >= p["min_duration"]))
    # If not selected, duration is 0
    opt.add(Implies(Not(selects[name]), durations[name] == 0))
    # Must be reachable from initial location and time
    opt.add(Implies(selects[name], starts[name] >= start_time + T[start_location][p["location"]]))

# Pairwise non-overlap with travel time using precedence variables
precedence = {}
n = len(people)
for i in range(n):
    for j in range(i + 1, n):
        pi = people[i]
        pj = people[j]
        key = (pi["name"], pj["name"])
        precedence[key] = Bool(f"before_{pi['name']}_then_{pj['name']}")
        # If i before j
        opt.add(Implies(And(selects[pi["name"]], selects[pj["name"]], precedence[key]),
                        ends[pi["name"]] + T[pi["location"]][pj["location"]] <= starts[pj["name"]]))
        # Else j before i
        opt.add(Implies(And(selects[pi["name"]], selects[pj["name"]], Not(precedence[key])),
                        ends[pj["name"]] + T[pj["location"]][pi["location"]] <= starts[pi["name"]]))

# Objective: maximize number of meetings, then total duration
count_meetings = Sum([If(selects[p["name"]], 1, 0) for p in people])
total_meeting_minutes = Sum([durations[p["name"]] for p in people])

opt.maximize(count_meetings)
opt.maximize(total_meeting_minutes)

if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    selected_meetings = []
    for p in people:
        name = p["name"]
        if is_true(m.evaluate(selects[name], model_completion=True)):
            s = m.evaluate(starts[name], model_completion=True).as_long()
            e = m.evaluate(ends[name], model_completion=True).as_long()
            selected_meetings.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e),
            })
    # Sort by start_time
    selected_meetings.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    print(json.dumps({"itinerary": selected_meetings}, ensure_ascii=False))