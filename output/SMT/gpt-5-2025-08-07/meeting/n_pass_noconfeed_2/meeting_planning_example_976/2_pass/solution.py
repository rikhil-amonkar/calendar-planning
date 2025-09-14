import json
from z3 import Int, Bool, Optimize, And, Or, Implies, If, sat

# Helper to convert (H, M) to minutes since midnight
def minutes(h, m):
    return h * 60 + m

# Helper to format minutes to H:MM (24-hour, no leading zero on hour)
def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes) between locations
travel = {
    "Embarcadero": {
        "Bayview": 21,
        "Chinatown": 7,
        "Alamo Square": 19,
        "Nob Hill": 10,
        "Presidio": 20,
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Fisherman's Wharf": 6,
        "Marina District": 12,
    },
    "Bayview": {
        "Embarcadero": 19,
        "Chinatown": 19,
        "Alamo Square": 16,
        "Nob Hill": 20,
        "Presidio": 32,
        "Union Square": 18,
        "The Castro": 19,
        "North Beach": 22,
        "Fisherman's Wharf": 25,
        "Marina District": 27,
    },
    "Chinatown": {
        "Embarcadero": 5,
        "Bayview": 20,
        "Alamo Square": 17,
        "Nob Hill": 9,
        "Presidio": 19,
        "Union Square": 7,
        "The Castro": 22,
        "North Beach": 3,
        "Fisherman's Wharf": 8,
        "Marina District": 12,
    },
    "Alamo Square": {
        "Embarcadero": 16,
        "Bayview": 16,
        "Chinatown": 15,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Bayview": 19,
        "Chinatown": 6,
        "Alamo Square": 11,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
    },
    "Presidio": {
        "Embarcadero": 20,
        "Bayview": 31,
        "Chinatown": 21,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
    },
    "Union Square": {
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Alamo Square": 15,
        "Nob Hill": 9,
        "Presidio": 24,
        "The Castro": 17,
        "North Beach": 10,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
    },
    "The Castro": {
        "Embarcadero": 22,
        "Bayview": 19,
        "Chinatown": 22,
        "Alamo Square": 8,
        "Nob Hill": 16,
        "Presidio": 20,
        "Union Square": 19,
        "North Beach": 20,
        "Fisherman's Wharf": 24,
        "Marina District": 21,
    },
    "North Beach": {
        "Embarcadero": 6,
        "Bayview": 25,
        "Chinatown": 6,
        "Alamo Square": 16,
        "Nob Hill": 7,
        "Presidio": 17,
        "Union Square": 7,
        "The Castro": 23,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Bayview": 26,
        "Chinatown": 12,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Marina District": 9,
    },
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Chinatown": 15,
        "Alamo Square": 15,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "The Castro": 22,
        "North Beach": 11,
        "Fisherman's Wharf": 10,
    },
}

# People data: name -> dict(location, start, end, min_duration)
people = {
    "Matthew": {"location": "Bayview", "start": minutes(19, 15), "end": minutes(22, 0), "min_duration": 120},
    "Karen": {"location": "Chinatown", "start": minutes(19, 15), "end": minutes(21, 15), "min_duration": 90},
    "Sarah": {"location": "Alamo Square", "start": minutes(20, 0), "end": minutes(21, 45), "min_duration": 105},
    "Jessica": {"location": "Nob Hill", "start": minutes(16, 30), "end": minutes(18, 45), "min_duration": 120},
    "Stephanie": {"location": "Presidio", "start": minutes(7, 30), "end": minutes(10, 15), "min_duration": 60},
    "Mary": {"location": "Union Square", "start": minutes(16, 45), "end": minutes(21, 30), "min_duration": 60},
    "Charles": {"location": "The Castro", "start": minutes(16, 30), "end": minutes(22, 0), "min_duration": 105},
    "Nancy": {"location": "North Beach", "start": minutes(14, 45), "end": minutes(20, 0), "min_duration": 15},
    "Thomas": {"location": "Fisherman's Wharf", "start": minutes(13, 30), "end": minutes(19, 0), "min_duration": 30},
    "Brian": {"location": "Marina District", "start": minutes(12, 15), "end": minutes(18, 0), "min_duration": 60},
}

start_location = "Embarcadero"
arrival_time = minutes(9, 0)

# Build Z3 model
opt = Optimize()
opt.set(priority='lex')

starts = {}
ends = {}
durs = {}
meets = {}

# Create variables and constraints per person
for name, info in people.items():
    s = Int(f"start_{name}")
    e = Int(f"end_{name}")
    d = Int(f"dur_{name}")
    m = Bool(f"meet_{name}")
    starts[name] = s
    ends[name] = e
    durs[name] = d
    meets[name] = m

    loc = info["location"]
    a_start = info["start"]
    a_end = info["end"]
    min_dur = info["min_duration"]
    window_len = a_end - a_start

    # Basic bounds
    opt.add(s >= 0, s <= 24 * 60)
    opt.add(e >= 0, e <= 24 * 60)
    opt.add(d >= 0)
    # Define end = start + duration
    opt.add(e == s + d)

    # If meeting, must be within availability window and meet min duration
    opt.add(Implies(m, And(s >= a_start, e <= a_end, d >= min_dur)))
    # If not meeting, duration zero; if meeting, duration <= window length
    opt.add(d <= If(m, window_len, 0))

    # Must be reachable from initial location at arrival time
    init_travel = travel[start_location][loc]
    opt.add(Implies(m, s >= arrival_time + init_travel))

# Pairwise non-overlap with travel feasibility
names = list(people.keys())
for i in range(len(names)):
    for j in range(i + 1, len(names)):
        ni = names[i]
        nj = names[j]
        li = people[ni]["location"]
        lj = people[nj]["location"]
        tij = travel[li][lj]
        tji = travel[lj][li]
        # If both meetings occur, then either i before j with travel or j before i with travel
        opt.add(
            Implies(
                And(meets[ni], meets[nj]),
                Or(ends[ni] + tij <= starts[nj], ends[nj] + tji <= starts[ni]),
            )
        )

# Objective 1: maximize number of people met
total_met = sum([If(meets[name], 1, 0) for name in names])
opt.maximize(total_met)

# Objective 2: maximize total meeting time
total_minutes = sum([durs[name] for name in names])
opt.maximize(total_minutes)

# Solve
res = opt.check()
if res != sat:
    output = {"itinerary": []}
    print(json.dumps(output, ensure_ascii=False))
else:
    model = opt.model()
    itinerary = []
    for name in names:
        if model.evaluate(meets[name], model_completion=True).is_true():
            s = model.evaluate(starts[name]).as_long()
            e = model.evaluate(ends[name]).as_long()
            loc = people[name]["location"]
            itinerary.append(
                {
                    "action": "meet",
                    "location": loc,
                    "person": name,
                    "start_time": fmt_time(s),
                    "end_time": fmt_time(e),
                }
            )

    # Sort by start_time
    itinerary.sort(
        key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1]))
    )

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))