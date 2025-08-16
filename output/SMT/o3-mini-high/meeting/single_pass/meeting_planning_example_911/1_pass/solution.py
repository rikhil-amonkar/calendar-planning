from z3 import *
import json

# Helper: convert HH:MM string to minutes since midnight
def to_minutes(time_str):
    hh, mm = time_str.split(":")
    return int(hh)*60 + int(mm)

# Data for friends: name, meeting location, availability (start and end in minutes) and minimum meeting duration (in minutes)
# Times are given in 24‐hour clock, expressed in minutes after midnight.
friends = [
    {"name": "Steven",    "location": "North Beach",       "avail_start": to_minutes("17:30"), "avail_end": to_minutes("20:30"), "min_duration": 15},
    {"name": "Sarah",     "location": "Golden Gate Park",  "avail_start": to_minutes("17:00"), "avail_end": to_minutes("19:15"), "min_duration": 75},
    {"name": "Brian",     "location": "Embarcadero",       "avail_start": to_minutes("14:15"), "avail_end": to_minutes("16:00"), "min_duration": 105},
    {"name": "Stephanie", "location": "Haight-Ashbury",    "avail_start": to_minutes("10:15"), "avail_end": to_minutes("12:15"), "min_duration": 75},
    {"name": "Melissa",   "location": "Richmond District", "avail_start": to_minutes("14:00"), "avail_end": to_minutes("19:30"), "min_duration": 30},
    {"name": "Nancy",     "location": "Nob Hill",          "avail_start": to_minutes("08:15"), "avail_end": to_minutes("12:45"), "min_duration": 90},
    {"name": "David",     "location": "Marina District",   "avail_start": to_minutes("11:15"), "avail_end": to_minutes("13:15"), "min_duration": 120},
    {"name": "James",     "location": "Presidio",          "avail_start": to_minutes("15:00"), "avail_end": to_minutes("18:15"), "min_duration": 120},
    {"name": "Elizabeth", "location": "Union Square",      "avail_start": to_minutes("11:30"), "avail_end": to_minutes("21:00"), "min_duration": 60},
    {"name": "Robert",    "location": "Financial District","avail_start": to_minutes("13:15"), "avail_end": to_minutes("15:15"), "min_duration": 45},
]

n = len(friends)

# Travel time data as provided.
# Each key is a (From, To)-tuple and value is time in minutes.
travel = {
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Financial District"): 21,

    ("North Beach", "The Castro"): 23,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Financial District"): 8,

    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Financial District"): 26,

    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 20,
    ("Embarcadero", "Richmond District"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,

    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Financial District"): 21,

    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Financial District"): 22,

    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Financial District"): 9,

    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Financial District"): 17,

    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Financial District"): 23,

    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Financial District"): 9,

    ("Financial District", "The Castro"): 20,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
}

# Our starting location is "The Castro", and we arrive at 09:00 (i.e. 540 minutes).
start_location = "The Castro"
start_time = to_minutes("09:00")

# Create an Optimize object (which supports maximization)
opt = Optimize()

# For each friend we create variables:
#   b[i]: Bool indicating whether we schedule a meeting with friend i.
#   s[i]: start time of the meeting (in minutes).
#   e[i]: end time of the meeting.
b_vars = [Bool(f"b_{i}") for i in range(n)]
s_vars = [Int(f"s_{i}") for i in range(n)]
e_vars = [Int(f"e_{i}") for i in range(n)]

# For each friend, if scheduled then meeting must:
# (i) occur in the friend’s available window;
# (ii) last at least the minimum duration;
# (iii) not start before you can get there from "The Castro".
for i, friend in enumerate(friends):
    opt.add(Implies(b_vars[i], s_vars[i] >= friend["avail_start"]))
    opt.add(Implies(b_vars[i], e_vars[i] <= friend["avail_end"]))
    opt.add(Implies(b_vars[i], e_vars[i] - s_vars[i] >= friend["min_duration"]))
    # Constraint from starting location (applies even if not first meeting)
    travel_from_start = travel.get((start_location, friend["location"]), 9999)
    opt.add(Implies(b_vars[i], s_vars[i] >= start_time + travel_from_start))
    # Bound times to a single day
    opt.add(s_vars[i] >= 0, e_vars[i] >= 0, s_vars[i] <= 1440, e_vars[i] <= 1440)
    # If not scheduled, force times to 0 (for determinacy)
    opt.add(Implies(Not(b_vars[i]), s_vars[i] == 0))
    opt.add(Implies(Not(b_vars[i]), e_vars[i] == 0))

# Now, for every pair of distinct meetings i,j that are both scheduled,
# we introduce a Boolean variable to decide their order.
# We only create one Boolean per unordered pair (i,j) with i<j.
order = {}
for i in range(n):
    for j in range(i+1, n):
        order[(i, j)] = Bool(f"order_{i}_{j}")
        # When both meetings are scheduled, we force one to come before the other.
        # We use the following constraints:
        # • If order[(i,j)] is True then friend i is scheduled before friend j:
        #       e[i] + travel_time( location_i -> location_j ) <= s[j]
        # • Otherwise (order[(i,j)] is False) friend j comes before friend i:
        #       e[j] + travel_time( location_j -> location_i ) <= s[i]
        travel_ij = travel.get((friends[i]["location"], friends[j]["location"]), 9999)
        travel_ji = travel.get((friends[j]["location"], friends[i]["location"]), 9999)
        opt.add(Implies(And(b_vars[i], b_vars[j], order[(i, j)]), s_vars[j] >= e_vars[i] + travel_ij))
        opt.add(Implies(And(b_vars[i], b_vars[j], Not(order[(i, j)])), s_vars[i] >= e_vars[j] + travel_ji))
        # (No need to force a choice when one or both meetings are not scheduled)

# Our goal is to maximize the number of meetings scheduled.
objective = Sum([If(b_vars[i], 1, 0) for i in range(n)])
opt.maximize(objective)

# Solve the optimization problem.
if opt.check() == sat:
    model = opt.model()

    # Gather the scheduled meetings (only those with b=True)
    scheduled_meetings = []
    for i in range(n):
        if model.evaluate(b_vars[i]):
            st = model.evaluate(s_vars[i]).as_long()
            et = model.evaluate(e_vars[i]).as_long()
            scheduled_meetings.append((st, et, friends[i]["name"], friends[i]["location"]))
    
    # Sort by start time.
    scheduled_meetings.sort(key=lambda x: x[0])
    
    # Format time as HH:MM.
    def format_time(t):
        return f"{t//60:02d}:{t%60:02d}"
    
    itinerary = []
    for st, et, name, loc in scheduled_meetings:
        itinerary.append({"action": "meet", "person": name, "start_time": format_time(st), "end_time": format_time(et)})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")