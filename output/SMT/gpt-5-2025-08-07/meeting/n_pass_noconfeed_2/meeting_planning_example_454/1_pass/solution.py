# SOLUTION:
import json
from z3 import Optimize, Bool, Int, And, Or, Not, Implies, If, Sum, sat

def m(h, mm):
    return h * 60 + mm

def fmt(mins):
    h = mins // 60
    mm = mins % 60
    return f"{h}:{mm:02d}"

# Travel times in minutes (asymmetric)
travel = {
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Mission District'): 26,

    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Golden Gate Park', 'Mission District'): 17,

    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Mission District'): 13,

    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Mission District'): 18,

    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Mission District'): 18,

    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'North Beach'): 17,
}

def tt(a, b):
    return travel[(a, b)]

start_location = "Presidio"
arrival_time = m(9, 0)

# Friends and their availabilities
friends = [
    {"name": "Jessica", "location": "Golden Gate Park", "start": m(13, 45), "end": m(15, 0), "min_dur": 30},
    {"name": "Ashley", "location": "Bayview", "start": m(17, 15), "end": m(20, 0), "min_dur": 105},
    {"name": "Ronald", "location": "Chinatown", "start": m(7, 15), "end": m(14, 45), "min_dur": 90},
    {"name": "William", "location": "North Beach", "start": m(13, 15), "end": m(20, 15), "min_dur": 15},
    {"name": "Daniel", "location": "Mission District", "start": m(7, 0), "end": m(11, 15), "min_dur": 105},
]

opt = Optimize()
opt.set(priority="lex")

meet = {}
start = {}
end = {}

# Variables and constraints for each friend
for f in friends:
    name = f["name"]
    meet[name] = Bool(f"meet_{name}")
    start[name] = Int(f"start_{name}")
    end[name] = Int(f"end_{name}")

    # Basic bounds
    opt.add(start[name] >= 0, start[name] <= 24*60)
    opt.add(end[name] >= 0, end[name] <= 24*60)

    # If not meeting, times are zero to avoid arbitrary values
    opt.add(Implies(Not(meet[name]), And(start[name] == 0, end[name] == 0)))

    # If meeting, enforce availability, minimum duration, and reachability from start
    opt.add(Implies(meet[name],
                    And(
                        start[name] >= f["start"],
                        end[name] <= f["end"],
                        end[name] - start[name] >= f["min_dur"],
                        start[name] >= arrival_time + tt(start_location, f["location"]),
                        end[name] > start[name]
                    )))

# Non-overlap with travel times between any two meetings
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        fi = friends[i]
        fj = friends[j]
        ni, nj = fi["name"], fj["name"]
        li, lj = fi["location"], fj["location"]

        opt.add(Implies(And(meet[ni], meet[nj]),
                        Or(
                            end[ni] + tt(li, lj) <= start[nj],
                            end[nj] + tt(lj, li) <= start[ni]
                        )))

# Objectives: maximize number of friends met, then maximize total meeting time
num_met = Sum([If(meet[f["name"]], 1, 0) for f in friends])
total_meeting_time = Sum([If(meet[f["name"]], end[f["name"]] - start[f["name"]], 0) for f in friends])
opt.maximize(num_met)
opt.maximize(total_meeting_time)

result = {}
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for f in friends:
        name = f["name"]
        if model.evaluate(meet[name]).is_true():
            s = model.evaluate(start[name]).as_long()
            e = model.evaluate(end[name]).as_long()
            schedule.append({
                "action": "meet",
                "location": f["location"],
                "person": name,
                "start_time": fmt(s),
                "end_time": fmt(e)
            })
    # Sort by start time
    schedule.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))
    result = {"itinerary": schedule}
else:
    result = {"itinerary": []}

print(json.dumps(result, ensure_ascii=False))