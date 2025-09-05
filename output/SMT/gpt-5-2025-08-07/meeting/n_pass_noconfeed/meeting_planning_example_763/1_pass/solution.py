import json
from z3 import Optimize, Int, Bool, And, Or, Not, Implies, If, Sum, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Locations
locations = [
    "Chinatown",
    "Embarcadero",
    "Pacific Heights",
    "Russian Hill",
    "Haight-Ashbury",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Sunset District",
    "The Castro",
]

# Travel times (in minutes), directed
travel = {
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,

    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,

    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "The Castro"): 16,

    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "The Castro"): 21,

    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "The Castro"): 6,

    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,

    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "The Castro"): 27,

    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "The Castro"): 17,

    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Sunset District"): 17,
}

# People and constraints
people = [
    {
        "name": "Richard",
        "location": "Embarcadero",
        "avail_start": minutes(15, 15),
        "avail_end": minutes(18, 45),
        "min_duration": 90
    },
    {
        "name": "Mark",
        "location": "Pacific Heights",
        "avail_start": minutes(15, 0),
        "avail_end": minutes(17, 0),
        "min_duration": 45
    },
    {
        "name": "Matthew",
        "location": "Russian Hill",
        "avail_start": minutes(17, 30),
        "avail_end": minutes(21, 0),
        "min_duration": 90
    },
    {
        "name": "Rebecca",
        "location": "Haight-Ashbury",
        "avail_start": minutes(14, 45),
        "avail_end": minutes(18, 0),
        "min_duration": 60
    },
    {
        "name": "Melissa",
        "location": "Golden Gate Park",
        "avail_start": minutes(13, 45),
        "avail_end": minutes(17, 30),
        "min_duration": 90
    },
    {
        "name": "Margaret",
        "location": "Fisherman's Wharf",
        "avail_start": minutes(14, 45),
        "avail_end": minutes(20, 15),
        "min_duration": 15
    },
    {
        "name": "Emily",
        "location": "Sunset District",
        "avail_start": minutes(15, 45),
        "avail_end": minutes(17, 0),
        "min_duration": 45
    },
    {
        "name": "George",
        "location": "The Castro",
        "avail_start": minutes(14, 0),
        "avail_end": minutes(16, 15),
        "min_duration": 75
    },
]

# Initial conditions
start_location = "Chinatown"
arrival_time = minutes(9, 0)

n = len(people)

opt = Optimize()

meet = [Bool(f"meet_{i}") for i in range(n)]
start_vars = [Int(f"start_{i}") for i in range(n)]
end_vars = [Int(f"end_{i}") for i in range(n)]

# Meeting window constraints
for i, p in enumerate(people):
    s = start_vars[i]
    e = end_vars[i]
    a_s = p["avail_start"]
    a_e = p["avail_end"]
    min_d = p["min_duration"]
    opt.add(Implies(meet[i], And(s >= a_s, e <= a_e, e - s >= min_d)))

# Pairwise ordering constraints using a boolean "i_before_j" for i<j
before = {}
def get_before(i, j):
    # returns Bool "i before j" for i<j; ensures a single variable per unordered pair
    key = (min(i, j), max(i, j))
    if key not in before:
        before[key] = Bool(f"before_{key[0]}_{key[1]}")
    # Return expression meaning "i before j"
    if i < j:
        return before[key]
    else:
        return Not(before[key])

def travel_time(loc_from, loc_to):
    return travel[(loc_from, loc_to)]

for i in range(n):
    for j in range(i + 1, n):
        pi = people[i]
        pj = people[j]
        t_ij = travel_time(pi["location"], pj["location"])
        t_ji = travel_time(pj["location"], pi["location"])
        b_ij = before[(i, j)] = Bool(f"before_{i}_{j}")
        # If both meetings occur, enforce that either i before j or j before i with proper timing
        opt.add(Implies(And(meet[i], meet[j], b_ij), start_vars[j] >= end_vars[i] + t_ij))
        opt.add(Implies(And(meet[i], meet[j], Not(b_ij)), start_vars[i] >= end_vars[j] + t_ji))

# Anchor to initial location: if meeting i is not after someone else, it must start after travel from start location
for i in range(n):
    pi = people[i]
    anchor_from_start = start_vars[i] >= arrival_time + travel_time(start_location, pi["location"])
    predecessors = []
    for j in range(n):
        if j == i:
            continue
        # j before i?
        predecessors.append(And(meet[j], get_before(j, i)))
    opt.add(Implies(meet[i], Or(anchor_from_start, Or(predecessors) if predecessors else anchor_from_start)))

# Objective: maximize number of friends met, then maximize total meeting time
meet_count = Sum([If(meet[i], 1, 0) for i in range(n)])
total_meeting_minutes = Sum([If(meet[i], end_vars[i] - start_vars[i], 0) for i in range(n)])
opt.maximize(meet_count)
opt.maximize(total_meeting_minutes)

result = {"itinerary": []}

if opt.check() == sat:
    model = opt.model()
    meetings = []
    for i, p in enumerate(people):
        if model.eval(meet[i], model_completion=True):
            start_t = model.eval(start_vars[i], model_completion=True).as_long()
            end_t = model.eval(end_vars[i], model_completion=True).as_long()
            meetings.append({
                "person": p["name"],
                "location": p["location"],
                "start": start_t,
                "end": end_t
            })
    # Sort by start time
    meetings.sort(key=lambda x: x["start"])
    for m in meetings:
        result["itinerary"].append({
            "action": "meet",
            "location": m["location"],
            "person": m["person"],
            "start_time": fmt_time(m["start"]),
            "end_time": fmt_time(m["end"])
        })

print(json.dumps(result, ensure_ascii=False, indent=2))