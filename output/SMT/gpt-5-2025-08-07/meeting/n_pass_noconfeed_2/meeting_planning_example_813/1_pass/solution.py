# SOLUTION:
import json
from z3 import Int, Bool, Optimize, If, And, Or, Not, Implies, Sum, sat

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (minutes) between locations
travel = {
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Union Square": 16, "Chinatown": 15,
        "Sunset District": 19, "Golden Gate Park": 18, "Financial District": 17,
        "Haight-Ashbury": 16, "Mission District": 20
    },
    "Embarcadero": {
        "Marina District": 12, "Bayview": 21, "Union Square": 10, "Chinatown": 7,
        "Sunset District": 30, "Golden Gate Park": 25, "Financial District": 5,
        "Haight-Ashbury": 21, "Mission District": 20
    },
    "Bayview": {
        "Marina District": 27, "Embarcadero": 19, "Union Square": 18, "Chinatown": 19,
        "Sunset District": 23, "Golden Gate Park": 22, "Financial District": 19,
        "Haight-Ashbury": 19, "Mission District": 13
    },
    "Union Square": {
        "Marina District": 18, "Embarcadero": 11, "Bayview": 15, "Chinatown": 7,
        "Sunset District": 27, "Golden Gate Park": 22, "Financial District": 9,
        "Haight-Ashbury": 18, "Mission District": 14
    },
    "Chinatown": {
        "Marina District": 12, "Embarcadero": 5, "Bayview": 20, "Union Square": 7,
        "Sunset District": 29, "Golden Gate Park": 23, "Financial District": 5,
        "Haight-Ashbury": 19, "Mission District": 17
    },
    "Sunset District": {
        "Marina District": 21, "Embarcadero": 30, "Bayview": 22, "Union Square": 30,
        "Chinatown": 30, "Golden Gate Park": 11, "Financial District": 30,
        "Haight-Ashbury": 15, "Mission District": 25
    },
    "Golden Gate Park": {
        "Marina District": 16, "Embarcadero": 25, "Bayview": 23, "Union Square": 22,
        "Chinatown": 23, "Sunset District": 10, "Financial District": 26,
        "Haight-Ashbury": 7, "Mission District": 17
    },
    "Financial District": {
        "Marina District": 15, "Embarcadero": 4, "Bayview": 19, "Union Square": 9,
        "Chinatown": 5, "Sunset District": 30, "Golden Gate Park": 23,
        "Haight-Ashbury": 19, "Mission District": 17
    },
    "Haight-Ashbury": {
        "Marina District": 17, "Embarcadero": 20, "Bayview": 18, "Union Square": 19,
        "Chinatown": 19, "Sunset District": 15, "Golden Gate Park": 7,
        "Financial District": 21, "Mission District": 11
    },
    "Mission District": {
        "Marina District": 19, "Embarcadero": 19, "Bayview": 14, "Union Square": 15,
        "Chinatown": 16, "Sunset District": 24, "Golden Gate Park": 17,
        "Financial District": 15, "Haight-Ashbury": 12
    }
}

# People and their availability/minimum meeting duration
people = {
    "Joshua":   {"location": "Embarcadero",       "start": 585,  "end": 1080, "min": 105},
    "Jeffrey":  {"location": "Bayview",           "start": 585,  "end": 1215, "min": 75},
    "Charles":  {"location": "Union Square",      "start": 645,  "end": 1215, "min": 120},
    "Joseph":   {"location": "Chinatown",         "start": 420,  "end": 930,  "min": 60},
    "Elizabeth":{"location": "Sunset District",   "start": 540,  "end": 585,  "min": 45},
    "Matthew":  {"location": "Golden Gate Park",  "start": 660,  "end": 1170, "min": 45},
    "Carol":    {"location": "Financial District","start": 645,  "end": 675,  "min": 15},
    "Paul":     {"location": "Haight-Ashbury",    "start": 1155, "end": 1230, "min": 15},
    "Rebecca":  {"location": "Mission District",  "start": 1020, "end": 1305, "min": 45},
}

start_location = "Marina District"
arrival_time = 540  # 9:00

# Z3 variables
opt = Optimize()
opt.set(priority='lex')

start_vars = {}
end_vars = {}
dur_vars = {}
attend_vars = {}

for p, info in people.items():
    s = Int(f"{p}_start")
    e = Int(f"{p}_end")
    d = Int(f"{p}_dur")
    a = Bool(f"{p}_attend")
    start_vars[p] = s
    end_vars[p] = e
    dur_vars[p] = d
    attend_vars[p] = a

    # Domains
    opt.add(s >= 0, s <= 24*60)
    opt.add(e >= 0, e <= 24*60)
    opt.add(d >= 0)

    # If attending, ensure within availability, durations, and sequence validity
    avail_start = people[p]["start"]
    avail_end = people[p]["end"]
    min_dur = people[p]["min"]
    loc = people[p]["location"]

    # Arrival feasibility from start location at 9:00
    travel_from_start = travel[start_location][loc]
    opt.add(Implies(a, s >= arrival_time + travel_from_start))

    # Availability and duration constraints
    opt.add(Implies(a, And(s >= avail_start, e <= avail_end, e >= s + min_dur, d == e - s)))
    # If not attending, zero duration and align start=end (free to be any time)
    opt.add(Implies(Not(a), And(d == 0, e == s)))

# Pairwise non-overlap with travel times for attended meetings
names = list(people.keys())
order_vars = {}
for i in range(len(names)):
    for j in range(i+1, len(names)):
        pi = names[i]
        pj = names[j]
        order = Bool(f"order_{pi}_before_{pj}")
        order_vars[(pi, pj)] = order
        li = people[pi]["location"]
        lj = people[pj]["location"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        # If both attended, enforce one ordering with travel times
        opt.add(Implies(And(attend_vars[pi], attend_vars[pj], order),
                        end_vars[pi] + tij <= start_vars[pj]))
        opt.add(Implies(And(attend_vars[pi], attend_vars[pj], Not(order)),
                        end_vars[pj] + tji <= start_vars[pi]))


# Objectives
count_attended = Sum([If(attend_vars[p], 1, 0) for p in names])
total_meeting_minutes = Sum([dur_vars[p] for p in names])
opt.maximize(count_attended)
opt.maximize(total_meeting_minutes)

# Solve
if opt.check() != sat:
    print(json.dumps({"itinerary": []}))
    exit(0)

m = opt.model()

# Build itinerary sorted by start time
itinerary = []
for p in names:
    if m.eval(attend_vars[p], model_completion=True):
        s = m.eval(start_vars[p], model_completion=True).as_long()
        e = m.eval(end_vars[p], model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "location": people[p]["location"],
            "person": p,
            "start_time": minutes_to_str(s),
            "end_time": minutes_to_str(e)
        })

# Sort by start_time (convert back to minutes for sorting)
def str_to_minutes(t):
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

itinerary.sort(key=lambda x: str_to_minutes(x["start_time"]))

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))