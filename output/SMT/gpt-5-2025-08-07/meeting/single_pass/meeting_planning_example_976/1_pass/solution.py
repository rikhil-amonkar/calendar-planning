# Solve the SF friend-meeting scheduling problem with Z3 and output an optimal itinerary.
# Objective: maximize the number of friends met, then maximize total meeting minutes.

from z3 import *
import json

def tmin(h, m):
    return h*60 + m

def hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Directed travel times (minutes)
T = {
    "Embarcadero": {
        "Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20,
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6, "Marina District": 12
    },
    "Bayview": {
        "Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32,
        "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25, "Marina District": 27
    },
    "Chinatown": {
        "Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19,
        "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8, "Marina District": 12
    },
    "Alamo Square": {
        "Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17,
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19, "Marina District": 15
    },
    "Nob Hill": {
        "Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17,
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10, "Marina District": 11
    },
    "Presidio": {
        "Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18,
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Fisherman's Wharf": 19, "Marina District": 11
    },
    "Union Square": {
        "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9,
        "Presidio": 24, "The Castro": 17, "North Beach": 10, "Fisherman's Wharf": 15, "Marina District": 18
    },
    "The Castro": {
        "Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16,
        "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 24, "Marina District": 21
    },
    "North Beach": {
        "Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16, "Nob Hill": 7,
        "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5, "Marina District": 9
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11,
        "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 6, "Marina District": 9
    },
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12,
        "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11, "Fisherman's Wharf": 10
    }
}

# People: name, location, availability window, minimum meeting duration (minutes)
people = [
    {"name": "Matthew", "loc": "Bayview", "start": tmin(19,15), "end": tmin(22,0), "min": 120},
    {"name": "Karen", "loc": "Chinatown", "start": tmin(19,15), "end": tmin(21,15), "min": 90},
    {"name": "Sarah", "loc": "Alamo Square", "start": tmin(20,0), "end": tmin(21,45), "min": 105},
    {"name": "Jessica", "loc": "Nob Hill", "start": tmin(16,30), "end": tmin(18,45), "min": 120},
    {"name": "Stephanie", "loc": "Presidio", "start": tmin(7,30), "end": tmin(10,15), "min": 60},
    {"name": "Mary", "loc": "Union Square", "start": tmin(16,45), "end": tmin(21,30), "min": 60},
    {"name": "Charles", "loc": "The Castro", "start": tmin(16,30), "end": tmin(22,0), "min": 105},
    {"name": "Nancy", "loc": "North Beach", "start": tmin(14,45), "end": tmin(20,0), "min": 15},
    {"name": "Thomas", "loc": "Fisherman's Wharf", "start": tmin(13,30), "end": tmin(19,0), "min": 30},
    {"name": "Brian", "loc": "Marina District", "start": tmin(12,15), "end": tmin(18,0), "min": 60},
]

origin = "Embarcadero"
origin_time = tmin(9,0)  # 09:00

N = len(people)
opt = Optimize()

meet = [Bool(f"meet_{i}") for i in range(N)]
start = [Int(f"start_{i}") for i in range(N)]
end = [Int(f"end_{i}") for i in range(N)]
dur = [Int(f"dur_{i}") for i in range(N)]

for i, p in enumerate(people):
    loc = p["loc"]
    # Domains
    opt.add(start[i] >= 0, start[i] <= 24*60)
    opt.add(end[i] >= 0, end[i] <= 24*60)
    opt.add(dur[i] >= 0, dur[i] <= 24*60)

    # If meeting, enforce window, min duration, duration relation, and reachability from origin at 09:00
    opt.add(Implies(meet[i], And(
        start[i] >= p["start"],
        end[i] <= p["end"],
        dur[i] >= p["min"],
        end[i] == start[i] + dur[i],
        start[i] >= origin_time + T[origin][loc]
    )))
    # If not meeting, set times to 0 to keep model tidy
    opt.add(Implies(Not(meet[i]), And(start[i] == 0, end[i] == 0, dur[i] == 0)))

# Non-overlap and travel-time constraints between any two selected meetings
for i in range(N):
    for j in range(i+1, N):
        ti_j = T[people[i]["loc"]][people[j]["loc"]]
        tj_i = T[people[j]["loc"]][people[i]["loc"]]
        opt.add(Implies(And(meet[i], meet[j]),
                        Or(start[j] >= end[i] + ti_j,
                           start[i] >= end[j] + tj_i)))

# Objectives: maximize number met, then maximize total meeting time
num_met = Sum([If(meet[i], 1, 0) for i in range(N)])
total_minutes = Sum([dur[i] for i in range(N)])
opt.maximize(num_met)
opt.maximize(total_minutes)

if opt.check() != sat:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))
else:
    m = opt.model()
    meetings = []
    for i, p in enumerate(people):
        if is_true(m.eval(meet[i], model_completion=True)):
            st = m.eval(start[i]).as_long()
            et = m.eval(end[i]).as_long()
            meetings.append({
                "action": "meet",
                "person": p["name"],
                "start_time": hhmm(st),
                "end_time": hhmm(et)
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start_time"])
    print("SOLUTION:")
    print(json.dumps({"itinerary": meetings}))