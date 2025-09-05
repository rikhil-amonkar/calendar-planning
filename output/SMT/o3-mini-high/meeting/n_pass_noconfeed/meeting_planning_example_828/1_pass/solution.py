import json
from z3 import *

def minutes_to_time(m):
    # Convert integer minutes to H:MM format (24-hour, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Data for friends' meetings
friends = [
    {"name": "Stephanie", "location": "Richmond District", "avail_start": 16*60+15, "avail_end": 21*60+30, "min_duration": 75},
    {"name": "William", "location": "Union Square", "avail_start": 10*60+45, "avail_end": 17*60+30, "min_duration": 45},
    {"name": "Elizabeth", "location": "Nob Hill", "avail_start": 12*60+15, "avail_end": 15*60,     "min_duration": 105},
    {"name": "Joseph", "location": "Fisherman's Wharf", "avail_start": 12*60+45, "avail_end": 14*60,  "min_duration": 75},
    {"name": "Anthony", "location": "Golden Gate Park", "avail_start": 13*60, "avail_end": 20*60+30,   "min_duration": 75},
    {"name": "Barbara", "location": "Embarcadero", "avail_start": 19*60+15, "avail_end": 20*60+30,      "min_duration": 75},
    {"name": "Carol", "location": "Financial District", "avail_start": 11*60+45, "avail_end": 16*60+15,  "min_duration": 60},
    {"name": "Sandra", "location": "North Beach", "avail_start": 10*60, "avail_end": 12*60+30,           "min_duration": 15},
    {"name": "Kenneth", "location": "Presidio", "avail_start": 21*60+15, "avail_end": 22*60+15,           "min_duration": 45},
]

# Travel times (in minutes) between locations (asymmetric in general)
travel_times = {
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Presidio"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Presidio"): 24,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Presidio"): 17,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Presidio"): 11,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Presidio"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Presidio"): 17,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
}

# Create an Optimize solver instance
opt = Optimize()

N = len(friends)
# Decision variables for each friend's meeting
x = [Bool(f"x_{i}") for i in range(N)]             # Whether to schedule the meeting
s_vars = [Int(f"s_{i}") for i in range(N)]           # Start time (in minutes)
e_vars = [Int(f"e_{i}") for i in range(N)]           # End time (in minutes)
order_vars = [Int(f"order_{i}") for i in range(N)]   # Order position (0 if not scheduled)

# K = total number of scheduled meetings
K = Int("K")
opt.add(K == Sum([If(x[i], 1, 0) for i in range(N)]))

# General time bounds for each meeting.
for i in range(N):
    opt.add(s_vars[i] >= 0, e_vars[i] <= 24*60, s_vars[i] <= e_vars[i])

# Each meeting's scheduling constraints: if scheduled, the meeting must occur within the friend's available window and last at least the minimum duration.
for i, friend in enumerate(friends):
    opt.add(Implies(x[i],
                    And(s_vars[i] >= friend["avail_start"],
                        e_vars[i] <= friend["avail_end"],
                        e_vars[i] - s_vars[i] >= friend["min_duration"])))
    # Order variable: if scheduled, order must be between 1 and K; if not, order is 0.
    opt.add(Implies(x[i], And(order_vars[i] >= 1, order_vars[i] <= K)))
    opt.add(Implies(Not(x[i]), order_vars[i] == 0))

# Ensure distinct order positions for scheduled meetings.
for i in range(N):
    for j in range(i+1, N):
        opt.add(Implies(And(x[i], x[j]), order_vars[i] != order_vars[j]))

# Force the order numbers to form a consecutive sequence from 1 to K.
for j in range(1, N+1):
    count_j = Sum([If(And(x[i], order_vars[i] == j), 1, 0) for i in range(N)])
    opt.add(If(K >= j, count_j == 1, count_j == 0))

# Chain constraints:
# The first scheduled meeting must be reachable from the Marina District (starting at 9:00 which is 540 minutes)
for i in range(N):
    loc = friends[i]["location"]
    travel_time = travel_times[("Marina District", loc)]
    opt.add(Implies(And(x[i], order_vars[i] == 1), s_vars[i] >= 540 + travel_time))

# For any two meetings, if one immediately follows the other in the itinerary,
# then the next meeting's start time must be at least the previous meeting's end time plus travel time.
for i in range(N):
    for j in range(N):
        if i != j:
            tt = travel_times.get((friends[i]["location"], friends[j]["location"]))
            if tt is not None:
                opt.add(Implies(And(x[i], x[j], order_vars[j] == order_vars[i] + 1),
                                s_vars[j] >= e_vars[i] + tt))

# Objective: Maximize the number of meetings scheduled.
opt.maximize(K)

# Check for satisfiability and extract the model.
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    scheduled = []
    for i in range(N):
        if is_true(model.evaluate(x[i])):
            order_val = model.evaluate(order_vars[i]).as_long()
            start_val = model.evaluate(s_vars[i]).as_long()
            end_val = model.evaluate(e_vars[i]).as_long()
            scheduled.append((order_val, friends[i]["name"], friends[i]["location"], start_val, end_val))
    scheduled.sort(key=lambda tup: tup[0])
    for order_val, name, location, start_val, end_val in scheduled:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": minutes_to_time(start_val),
            "end_time": minutes_to_time(end_val)
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))