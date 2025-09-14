import json
from z3 import *

def time_to_minutes(t):
    # t like "H:MM" or "HH:MM"
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Locations
locations = [
    "Presidio",
    "Pacific Heights",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Marina District",
    "Alamo Square",
    "Sunset District",
    "Nob Hill",
    "North Beach",
]

# Travel times (minutes) as given (directional)
travel_times = {
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,

    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "North Beach"): 9,

    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "North Beach"): 23,

    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,

    ("Marina District", "Presidio"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "North Beach"): 11,

    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,

    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "North Beach"): 28,

    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "North Beach"): 8,

    ("North Beach", "Presidio"): 17,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Nob Hill"): 7,
}

def travel(a, b):
    return travel_times[(a, b)]

# People constraints
people = [
    {"name": "Kevin", "location": "Pacific Heights", "avail_start": time_to_minutes("7:15"), "avail_end": time_to_minutes("8:45"), "min_dur": 90},
    {"name": "Michelle", "location": "Golden Gate Park", "avail_start": time_to_minutes("20:00"), "avail_end": time_to_minutes("21:00"), "min_dur": 15},
    {"name": "Emily", "location": "Fisherman's Wharf", "avail_start": time_to_minutes("16:15"), "avail_end": time_to_minutes("19:00"), "min_dur": 30},
    {"name": "Mark", "location": "Marina District", "avail_start": time_to_minutes("18:15"), "avail_end": time_to_minutes("19:45"), "min_dur": 75},
    {"name": "Barbara", "location": "Alamo Square", "avail_start": time_to_minutes("17:00"), "avail_end": time_to_minutes("19:00"), "min_dur": 120},
    {"name": "Laura", "location": "Sunset District", "avail_start": time_to_minutes("19:00"), "avail_end": time_to_minutes("21:15"), "min_dur": 75},
    {"name": "Mary", "location": "Nob Hill", "avail_start": time_to_minutes("17:30"), "avail_end": time_to_minutes("19:00"), "min_dur": 45},
    {"name": "Helen", "location": "North Beach", "avail_start": time_to_minutes("11:00"), "avail_end": time_to_minutes("12:15"), "min_dur": 45},
]

# Day start and starting location
day_start = time_to_minutes("9:00")
start_location = "Presidio"

opt = Optimize()
opt.set("opt.priority", "lex")

# Variables
starts = {}
ends = {}
meets = {}
durs = {}

max_time = 24 * 60

for p in people:
    name = p["name"]
    s = Int(f"start_{name}")
    e = Int(f"end_{name}")
    m = Int(f"meet_{name}")  # 0 or 1
    d = Int(f"dur_{name}")

    starts[name] = s
    ends[name] = e
    meets[name] = m
    durs[name] = d

    # Domains
    opt.add(m >= 0, m <= 1)
    opt.add(s >= 0, s <= max_time)
    opt.add(e >= 0, e <= max_time)
    opt.add(d >= 0)

    # Within availability
    opt.add(s >= p["avail_start"])
    opt.add(e <= p["avail_end"])

    # Duration definition and gating by meet
    opt.add(d == e - s)
    opt.add(d >= p["min_dur"] * m)
    # If not meeting, duration must be 0; if meeting, duration <= full window
    opt.add(d <= (p["avail_end"] - p["avail_start"]) * m)

    # Reachability from starting point if meeting
    opt.add(Implies(m == 1, s >= day_start + travel(start_location, p["location"])))

# Pairwise non-overlap with travel time if both are met
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        pi = people[i]
        pj = people[j]
        ni = pi["name"]
        nj = pj["name"]
        ti_j = travel(pi["location"], pj["location"])
        tj_i = travel(pj["location"], pi["location"])
        # If both meetings occur, enforce travel-time separated order
        opt.add(Implies(And(meets[ni] == 1, meets[nj] == 1),
                        Or(ends[ni] + ti_j <= starts[nj],
                           ends[nj] + tj_i <= starts[ni])))

# Objective: maximize number of people met, then maximize total meeting time
total_met = Sum([meets[p["name"]] for p in people])
total_minutes = Sum([durs[p["name"]] for p in people])

opt.maximize(total_met)
opt.maximize(total_minutes)

if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for p in people:
        name = p["name"]
        if model[meets[name]].as_long() == 1:
            s = model[starts[name]].as_long()
            e = model[ends[name]].as_long()
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": minutes_to_time(s),
                "end_time": minutes_to_time(e)
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    output = {"itinerary": itinerary}
else:
    output = {"itinerary": []}

print(json.dumps(output, indent=2))