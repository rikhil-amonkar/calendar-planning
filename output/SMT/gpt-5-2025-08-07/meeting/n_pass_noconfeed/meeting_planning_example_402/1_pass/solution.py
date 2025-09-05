# SOLUTION:
import json
from z3 import Int, Bool, If, And, Or, Implies, Optimize, sat

def to_minutes(t):
    # t like "9:00" or "17:30" 24-hour, may not have leading zero
    h, m = map(int, t.split(":"))
    return h * 60 + m

def from_minutes(m):
    h = m // 60
    mn = m % 60
    return f"{h}:{mn:02d}"

# Data
locations = [
    "Golden Gate Park",
    "Haight-Ashbury",
    "Sunset District",
    "Marina District",
    "Financial District",
    "Union Square"
]

# Travel times (minutes), directional as provided
t = {}
for a in locations:
    t[a] = {}
# Fill in times
t["Golden Gate Park"]["Haight-Ashbury"] = 7
t["Golden Gate Park"]["Sunset District"] = 10
t["Golden Gate Park"]["Marina District"] = 16
t["Golden Gate Park"]["Financial District"] = 26
t["Golden Gate Park"]["Union Square"] = 22

t["Haight-Ashbury"]["Golden Gate Park"] = 7
t["Haight-Ashbury"]["Sunset District"] = 15
t["Haight-Ashbury"]["Marina District"] = 17
t["Haight-Ashbury"]["Financial District"] = 21
t["Haight-Ashbury"]["Union Square"] = 17

t["Sunset District"]["Golden Gate Park"] = 11
t["Sunset District"]["Haight-Ashbury"] = 15
t["Sunset District"]["Marina District"] = 21
t["Sunset District"]["Financial District"] = 30
t["Sunset District"]["Union Square"] = 30

t["Marina District"]["Golden Gate Park"] = 18
t["Marina District"]["Haight-Ashbury"] = 16
t["Marina District"]["Sunset District"] = 19
t["Marina District"]["Financial District"] = 17
t["Marina District"]["Union Square"] = 16

t["Financial District"]["Golden Gate Park"] = 23
t["Financial District"]["Haight-Ashbury"] = 19
t["Financial District"]["Sunset District"] = 31
t["Financial District"]["Marina District"] = 15
t["Financial District"]["Union Square"] = 9

t["Union Square"]["Golden Gate Park"] = 22
t["Union Square"]["Haight-Ashbury"] = 18
t["Union Square"]["Sunset District"] = 26
t["Union Square"]["Marina District"] = 18
t["Union Square"]["Financial District"] = 9

# Participants and constraints
friends = {
    "Sarah": {
        "location": "Haight-Ashbury",
        "avail_start": to_minutes("17:00"),
        "avail_end": to_minutes("21:30"),
        "min_duration": 105
    },
    "Patricia": {
        "location": "Sunset District",
        "avail_start": to_minutes("17:00"),
        "avail_end": to_minutes("19:45"),
        "min_duration": 45
    },
    "Matthew": {
        "location": "Marina District",
        "avail_start": to_minutes("9:15"),
        "avail_end": to_minutes("12:00"),
        "min_duration": 15
    },
    "Joseph": {
        "location": "Financial District",
        "avail_start": to_minutes("14:15"),
        "avail_end": to_minutes("18:45"),
        "min_duration": 30
    },
    "Robert": {
        "location": "Union Square",
        "avail_start": to_minutes("10:15"),
        "avail_end": to_minutes("21:45"),
        "min_duration": 15
    }
}

start_location = "Golden Gate Park"
arrival_time = to_minutes("9:00")
day_end = 24 * 60

# Z3 variables
opt = Optimize()
opt.set(priority='lex')

start_vars = {}
end_vars = {}
meet_bools = {}

for person, info in friends.items():
    s = Int(f"{person}_start")
    e = Int(f"{person}_end")
    m = Bool(f"{person}_meet")
    start_vars[person] = s
    end_vars[person] = e
    meet_bools[person] = m

    # Domains
    opt.add(And(s >= 0, s <= day_end, e >= 0, e <= day_end))
    opt.add(Implies(m, And(
        s >= info["avail_start"],
        e <= info["avail_end"],
        e > s,
        e - s >= info["min_duration"]
    )))
    # Physical reachability from starting point at 9:00 (safe lower bound)
    # If meeting occurs, cannot start earlier than earliest possible arrival from start:
    earliest_from_start = arrival_time + t[start_location][info["location"]]
    opt.add(Implies(m, s >= earliest_from_start))

# Pairwise non-overlap with travel times between any two meetings that both occur
people = list(friends.keys())
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        p = people[i]
        q = people[j]
        loc_p = friends[p]["location"]
        loc_q = friends[q]["location"]
        travel_pq = t[loc_p][loc_q]
        travel_qp = t[loc_q][loc_p]
        # If both meetings happen, enforce that either p before q (with travel) or q before p (with travel)
        opt.add(Implies(And(meet_bools[p], meet_bools[q]),
                        Or(end_vars[p] + travel_pq <= start_vars[q],
                           end_vars[q] + travel_qp <= start_vars[p])))

# Objective: maximize number of friends met, then maximize total meeting time
meet_count = sum([If(meet_bools[p], 1, 0) for p in people])
total_duration = sum([If(meet_bools[p], end_vars[p] - start_vars[p], 0) for p in people])
opt.maximize(meet_count)
opt.maximize(total_duration)

if opt.check() != sat:
    # In case no solution (shouldn't happen with given data), output empty itinerary
    print(json.dumps({"itinerary": []}))
else:
    model = opt.model()
    itinerary = []
    for person in people:
        if model.evaluate(meet_bools[person], model_completion=True):
            s_val = model.evaluate(start_vars[person]).as_long()
            e_val = model.evaluate(end_vars[person]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[person]["location"],
                "person": person,
                "start_time": from_minutes(s_val),
                "end_time": from_minutes(e_val)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: to_minutes(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))