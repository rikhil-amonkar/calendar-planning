import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def parse_time_str(t):
    h, m = map(int, t.split(":"))
    return minutes(h, m)

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Union Square",
    "The Castro",
    "North Beach",
    "Embarcadero",
    "Alamo Square",
    "Nob Hill",
    "Presidio",
    "Fisherman's Wharf",
    "Mission District",
    "Haight-Ashbury",
]

# Travel times (minutes) directional
T = {
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Embarcadero": 11,
        "Alamo Square": 15,
        "Nob Hill": 9,
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Mission District": 14,
        "Haight-Ashbury": 18,
    },
    "The Castro": {
        "Union Square": 19,
        "North Beach": 20,
        "Embarcadero": 22,
        "Alamo Square": 8,
        "Nob Hill": 16,
        "Presidio": 20,
        "Fisherman's Wharf": 24,
        "Mission District": 7,
        "Haight-Ashbury": 6,
    },
    "North Beach": {
        "Union Square": 7,
        "The Castro": 23,
        "Embarcadero": 6,
        "Alamo Square": 16,
        "Nob Hill": 7,
        "Presidio": 17,
        "Fisherman's Wharf": 5,
        "Mission District": 18,
        "Haight-Ashbury": 18,
    },
    "Embarcadero": {
        "Union Square": 10,
        "The Castro": 25,
        "North Beach": 5,
        "Alamo Square": 19,
        "Nob Hill": 10,
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Mission District": 20,
        "Haight-Ashbury": 21,
    },
    "Alamo Square": {
        "Union Square": 14,
        "The Castro": 8,
        "North Beach": 15,
        "Embarcadero": 16,
        "Nob Hill": 11,
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Mission District": 10,
        "Haight-Ashbury": 5,
    },
    "Nob Hill": {
        "Union Square": 7,
        "The Castro": 17,
        "North Beach": 8,
        "Embarcadero": 9,
        "Alamo Square": 11,
        "Presidio": 17,
        "Fisherman's Wharf": 10,
        "Mission District": 13,
        "Haight-Ashbury": 13,
    },
    "Presidio": {
        "Union Square": 22,
        "The Castro": 21,
        "North Beach": 18,
        "Embarcadero": 20,
        "Alamo Square": 19,
        "Nob Hill": 18,
        "Fisherman's Wharf": 19,
        "Mission District": 26,
        "Haight-Ashbury": 15,
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "The Castro": 27,
        "North Beach": 6,
        "Embarcadero": 8,
        "Alamo Square": 21,
        "Nob Hill": 11,
        "Presidio": 17,
        "Mission District": 22,
        "Haight-Ashbury": 22,
    },
    "Mission District": {
        "Union Square": 15,
        "The Castro": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Alamo Square": 11,
        "Nob Hill": 12,
        "Presidio": 25,
        "Fisherman's Wharf": 22,
        "Haight-Ashbury": 12,
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "The Castro": 6,
        "North Beach": 19,
        "Embarcadero": 20,
        "Alamo Square": 5,
        "Nob Hill": 15,
        "Presidio": 15,
        "Fisherman's Wharf": 23,
        "Mission District": 11,
    },
}

# People constraints
people = [
    {"name": "Melissa", "location": "The Castro", "start": minutes(20,15), "end": minutes(21,15), "min_dur": 30},
    {"name": "Kimberly", "location": "North Beach", "start": minutes(7,0), "end": minutes(10,30), "min_dur": 15},
    {"name": "Joseph", "location": "Embarcadero", "start": minutes(15,30), "end": minutes(19,30), "min_dur": 75},
    {"name": "Barbara", "location": "Alamo Square", "start": minutes(20,45), "end": minutes(21,45), "min_dur": 15},
    {"name": "Kenneth", "location": "Nob Hill", "start": minutes(12,15), "end": minutes(17,15), "min_dur": 105},
    {"name": "Joshua", "location": "Presidio", "start": minutes(16,30), "end": minutes(18,15), "min_dur": 105},
    {"name": "Brian", "location": "Fisherman's Wharf", "start": minutes(9,30), "end": minutes(15,30), "min_dur": 45},
    {"name": "Steven", "location": "Mission District", "start": minutes(19,30), "end": minutes(21,0), "min_dur": 90},
    {"name": "Betty", "location": "Haight-Ashbury", "start": minutes(19,0), "end": minutes(20,30), "min_dur": 90},
]

start_at_loc = "Union Square"
arrive_time = minutes(9, 0)

# Z3 variables
opt = Optimize()

meet = {}
from_start = {}
start_time = {}
end_time = {}
duration = {}

for p in people:
    n = p["name"]
    meet[n] = Bool(f"meet_{n}")
    from_start[n] = Bool(f"from_start_{n}")
    start_time[n] = Int(f"start_{n}")
    end_time[n] = Int(f"end_{n}")
    duration[n] = Int(f"dur_{n}")

    # Domains
    opt.add(start_time[n] >= 0, start_time[n] <= 24*60)
    opt.add(end_time[n] >= 0, end_time[n] <= 24*60)
    opt.add(duration[n] >= 0)

    # Meeting feasibility within availability
    avail_start = p["start"]
    avail_end = p["end"]
    min_d = p["min_dur"]
    max_d = avail_end - avail_start

    opt.add(Implies(meet[n],
                    And(start_time[n] >= avail_start,
                        end_time[n] <= avail_end,
                        end_time[n] == start_time[n] + duration[n],
                        duration[n] >= min_d,
                        duration[n] <= max_d)))

    # If not meeting, zero duration and times set to 0 for cleanliness
    opt.add(Implies(Not(meet[n]),
                    And(duration[n] == 0, start_time[n] == 0, end_time[n] == 0)))

    # from_start implies being met and respecting travel from initial location
    travel_from_start = T[start_at_loc][p["location"]]
    opt.add(Implies(from_start[n],
                    And(meet[n],
                        start_time[n] >= arrive_time + travel_from_start)))

# Pairwise non-overlap with travel times
for i in range(len(people)):
    for j in range(i+1, len(people)):
        pi = people[i]
        pj = people[j]
        ni = pi["name"]
        nj = pj["name"]
        ti_to_j = T[pi["location"]][pj["location"]]
        tj_to_i = T[pj["location"]][pi["location"]]
        opt.add(Implies(And(meet[ni], meet[nj]),
                        Or(start_time[nj] >= end_time[ni] + ti_to_j,
                           start_time[ni] >= end_time[nj] + tj_to_i)))

# Connectivity: each met meeting must have a predecessor or be from_start
for p in people:
    n = p["name"]
    preds = []
    for q in people:
        m = q["name"]
        if m == n:
            continue
        t_q_to_p = T[q["location"]][p["location"]]
        preds.append(And(meet[m], start_time[n] >= end_time[m] + t_q_to_p))
    # Or over predecessors plus from_start
    if preds:
        opt.add(Implies(meet[n], Or(from_start[n], Or(*preds))))
    else:
        opt.add(Implies(meet[n], from_start[n]))

# Exactly one start if any meetings; else none
any_meet = Or(*[meet[p["name"]] for p in people]) if people else False
sum_from_start = Sum([If(from_start[p["name"]], 1, 0) for p in people])
opt.add(Implies(any_meet, sum_from_start == 1))
opt.add(Implies(Not(any_meet), sum_from_start == 0))

# Objectives: maximize number of meetings, then total meeting minutes
total_met = Sum([If(meet[p["name"]], 1, 0) for p in people])
total_minutes = Sum([duration[p["name"]] for p in people])
opt.maximize(total_met)
opt.maximize(total_minutes)

result = opt.check()
itinerary = []
if result == sat:
    model = opt.model()
    # Collect met meetings
    items = []
    for p in people:
        n = p["name"]
        if is_true(model.evaluate(meet[n])):
            st = model.evaluate(start_time[n]).as_long()
            en = model.evaluate(end_time[n]).as_long()
            items.append({
                "action": "meet",
                "location": p["location"],
                "person": n,
                "start": st,
                "end": en
            })
    # Sort by start time
    items.sort(key=lambda x: x["start"])
    # Format times
    for it in items:
        itinerary.append({
            "action": "meet",
            "location": it["location"],
            "person": it["person"],
            "start_time": minutes_to_str(it["start"]),
            "end_time": minutes_to_str(it["end"])
        })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False, indent=2))