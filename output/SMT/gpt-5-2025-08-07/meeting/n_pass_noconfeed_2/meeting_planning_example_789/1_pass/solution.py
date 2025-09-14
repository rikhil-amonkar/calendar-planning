import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (directed, minutes)
travel = {
    "Union Square": {
        "Russian Hill": 13, "Alamo Square": 15, "Haight-Ashbury": 18, "Marina District": 18,
        "Bayview": 15, "Chinatown": 7, "Presidio": 24, "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10, "Alamo Square": 15, "Haight-Ashbury": 17, "Marina District": 7,
        "Bayview": 23, "Chinatown": 9, "Presidio": 14, "Sunset District": 23
    },
    "Alamo Square": {
        "Union Square": 14, "Russian Hill": 13, "Haight-Ashbury": 5, "Marina District": 15,
        "Bayview": 16, "Chinatown": 15, "Presidio": 17, "Sunset District": 16
    },
    "Haight-Ashbury": {
        "Union Square": 19, "Russian Hill": 17, "Alamo Square": 5, "Marina District": 17,
        "Bayview": 18, "Chinatown": 19, "Presidio": 15, "Sunset District": 15
    },
    "Marina District": {
        "Union Square": 16, "Russian Hill": 8, "Alamo Square": 15, "Haight-Ashbury": 16,
        "Bayview": 27, "Chinatown": 15, "Presidio": 10, "Sunset District": 19
    },
    "Bayview": {
        "Union Square": 18, "Russian Hill": 23, "Alamo Square": 16, "Haight-Ashbury": 19,
        "Marina District": 27, "Chinatown": 19, "Presidio": 32, "Sunset District": 23
    },
    "Chinatown": {
        "Union Square": 7, "Russian Hill": 7, "Alamo Square": 17, "Haight-Ashbury": 19,
        "Marina District": 12, "Bayview": 20, "Presidio": 19, "Sunset District": 29
    },
    "Presidio": {
        "Union Square": 22, "Russian Hill": 14, "Alamo Square": 19, "Haight-Ashbury": 15,
        "Marina District": 11, "Bayview": 31, "Chinatown": 21, "Sunset District": 15
    },
    "Sunset District": {
        "Union Square": 30, "Russian Hill": 24, "Alamo Square": 17, "Haight-Ashbury": 15,
        "Marina District": 21, "Bayview": 22, "Chinatown": 30, "Presidio": 16
    }
}

# People, locations, availability windows, and minimum meeting durations (minutes)
people = {
    "Betty":    {"location": "Russian Hill",   "start": minutes(7,0),   "end": minutes(16,45), "min_duration": 105},
    "Melissa":  {"location": "Alamo Square",   "start": minutes(9,30),  "end": minutes(17,15), "min_duration": 105},
    "Joshua":   {"location": "Haight-Ashbury", "start": minutes(12,15), "end": minutes(19,0),  "min_duration": 90},
    "Jeffrey":  {"location": "Marina District","start": minutes(12,15), "end": minutes(18,0),  "min_duration": 45},
    "James":    {"location": "Bayview",        "start": minutes(7,30),  "end": minutes(20,0),  "min_duration": 90},
    "Anthony":  {"location": "Chinatown",      "start": minutes(11,45), "end": minutes(13,30), "min_duration": 75},
    "Timothy":  {"location": "Presidio",       "start": minutes(12,30), "end": minutes(14,45), "min_duration": 90},
    "Emily":    {"location": "Sunset District","start": minutes(19,30), "end": minutes(21,30), "min_duration": 120}
}

start_location = "Union Square"
day_start = minutes(9,0)  # 9:00

# Z3 model
opt = Optimize()

# Variables for each person
s_vars = {}   # start times
e_vars = {}   # end times
met_vars = {} # whether we meet them

for name, info in people.items():
    s = Int(f"s_{name}")
    e = Int(f"e_{name}")
    met = Bool(f"met_{name}")
    s_vars[name] = s
    e_vars[name] = e
    met_vars[name] = met

    # Meeting duration fixed to minimum required if met, else e == s (no meeting)
    duration = info["min_duration"]
    # Availability constraints only if met
    opt.add(Implies(met, And(
        s >= info["start"],
        e <= info["end"],
        e == s + duration,
        s >= day_start + travel[start_location][info["location"]]
    )))
    # If not met, ensure zero duration (e == s) to keep times bounded and harmless
    opt.add(Implies(Not(met), e == s))

# Pairwise sequencing with travel time if both are met
names = list(people.keys())
for i in range(len(names)):
    for j in range(i+1, len(names)):
        ni = names[i]; nj = names[j]
        li = people[ni]["location"]; lj = people[nj]["location"]
        ti_to_j = travel[li][lj]
        tj_to_i = travel[lj][li]
        si = s_vars[ni]; ei = e_vars[ni]
        sj = s_vars[nj]; ej = e_vars[nj]
        mi = met_vars[ni]; mj = met_vars[nj]
        opt.add(Implies(And(mi, mj),
                        Or(ei + ti_to_j <= sj,
                           ej + tj_to_i <= si)))

# Objective: maximize number of friends met
total_met = Sum([If(met_vars[n], 1, 0) for n in names])
opt.maximize(total_met)

# Tie-breaker: maximize total minutes met (prefers longer meetings if equal count)
total_minutes = Sum([If(met_vars[n], people[n]["min_duration"], 0) for n in names])
opt.maximize(total_minutes)

# Solve
if opt.check() != sat:
    result = {"itinerary": []}
    print(json.dumps(result, ensure_ascii=False, indent=2))
else:
    model = opt.model()
    # Build itinerary from met friends
    itinerary = []
    for name in names:
        if is_true(model.eval(met_vars[name])):
            s = model.eval(s_vars[name]).as_long()
            e = model.eval(e_vars[name]).as_long()
            itinerary.append({
                "action": "meet",
                "location": people[name]["location"],
                "person": name,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })
    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0])*60 + int(x["start_time"].split(":")[1])))
    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False, indent=2))