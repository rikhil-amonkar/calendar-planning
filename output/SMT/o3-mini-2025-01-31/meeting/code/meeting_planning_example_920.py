from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# All times are measured in minutes relative to your arrival at Pacific Heights at 9:00AM (time = 0).
# Times are computed from the clock:
#   9:00AM => 0 minutes.
#
# 1. Daniel at North Beach from 12:15PM to 3:30PM; min meeting = 30 minutes.
#    [195, 390]
# 2. Mark at Nob Hill from 8:30PM to 10:00PM; min meeting = 90 minutes.
#    [690, 780]
# 3. Karen at Golden Gate Park from 12:45PM to 3:15PM; min meeting = 15 minutes.
#    [225, 375]
# 4. Nancy at Sunset District from 3:15PM to 8:30PM; min meeting = 75 minutes.
#    [375, 690]
# 5. Deborah at Financial District from 9:00AM to 11:15AM; min meeting = 30 minutes.
#    [0, 135]
# 6. Margaret at Fisherman's Wharf from 4:00PM to 9:30PM; min meeting = 75 minutes.
#    [420, 750]
# 7. Jessica at Haight-Ashbury from 4:45PM to 9:15PM; min meeting = 60 minutes.
#    [465, 735]
# 8. Thomas at Presidio from 6:15PM to 8:30PM; min meeting = 105 minutes.
#    [555, 690]
# 9. Lisa at Union Square from 2:30PM to 4:15PM; min meeting = 30 minutes.
#    [330, 435]
# 10. Jason at Marina District from 11:15AM to 2:00PM; min meeting = 60 minutes.
#     [135, 300]
friends = [
    {"name": "Daniel",   "location": "North Beach",       "avail_start": 195, "avail_end": 390, "duration": 30},
    {"name": "Mark",     "location": "Nob Hill",          "avail_start": 690, "avail_end": 780, "duration": 90},
    {"name": "Karen",    "location": "Golden Gate Park",  "avail_start": 225, "avail_end": 375, "duration": 15},
    {"name": "Nancy",    "location": "Sunset District",   "avail_start": 375, "avail_end": 690, "duration": 75},
    {"name": "Deborah",  "location": "Financial District","avail_start": 0,   "avail_end": 135, "duration": 30},
    {"name": "Margaret", "location": "Fisherman's Wharf", "avail_start": 420, "avail_end": 750, "duration": 75},
    {"name": "Jessica",  "location": "Haight-Ashbury",    "avail_start": 465, "avail_end": 735, "duration": 60},
    {"name": "Thomas",   "location": "Presidio",          "avail_start": 555, "avail_end": 690, "duration": 105},
    {"name": "Lisa",     "location": "Union Square",      "avail_start": 330, "avail_end": 435, "duration": 30},
    {"name": "Jason",    "location": "Marina District",   "avail_start": 135, "avail_end": 300, "duration": 60},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Pacific Heights",
    "North Beach",
    "Nob Hill",
    "Golden Gate Park",
    "Sunset District",
    "Financial District",
    "Fisherman's Wharf",
    "Haight-Ashbury",
    "Presidio",
    "Union Square",
    "Marina District",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# Each key is a tuple (origin, destination).
travel = {
    # From Pacific Heights:
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Marina District"): 6,

    # From North Beach:
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Marina District"): 9,

    # From Nob Hill:
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Marina District"): 11,

    # From Golden Gate Park:
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Marina District"): 16,

    # From Sunset District:
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Marina District"): 21,

    # From Financial District:
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Marina District"): 15,

    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,

    # From Haight-Ashbury:
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Marina District"): 17,

    # From Presidio:
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Marina District"): 11,

    # From Union Square:
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Marina District"): 18,

    # From Marina District:
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
}

# Helper function to get travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use the Optimize() solver to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i, x[i] is True if you meet friend i.
# start[i] is the meeting start time (in minutes relative to 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival location is Pacific Heights at time 0.
arrival_location = "Pacific Heights"
arrival_time = 0

# For each friend scheduled, enforce:
#   - The meeting start is no earlier than the friend’s available start.
#   - The meeting (start + duration) finishes by the available end.
#   - There is enough travel time from the starting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Pairwise non-overlap constraints:
# For any two meetings i and j that are both scheduled, ensure that either
# meeting i (plus its duration and travel time from location i to j) finishes
# before meeting j starts OR vice versa.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        no_overlap = Or(
            start[i] + dur_i + travel_i_j <= start[j],
            start[j] + dur_j + travel_j_i <= start[i]
        )
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the schedule.
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            t_val = model.evaluate(start[i]).as_long()
            schedule.append((t_val, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            # Convert minutes relative to 9:00AM to HH:MM.
            total = 540 + minutes  # since 9:00AM is 540 minutes after midnight.
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")