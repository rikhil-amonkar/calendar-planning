from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# Times are given in minutes relative to 9:00AM at Marina District (time = 0).
# 1. Joseph at Golden Gate Park, available from 6:45PM to 8:30PM => [585, 690], min meeting = 75 minutes.
# 2. Emily at North Beach, available from 2:45PM to 7:45PM => [345, 645], min meeting = 105 minutes.
# 3. Jeffrey at The Castro, available from 4:30PM to 9:00PM => [450, 720], min meeting = 120 minutes.
# 4. Sarah at Russian Hill, available from 5:45PM to 8:45PM => [525, 705], min meeting = 45 minutes.
# 5. Jessica at Nob Hill, available from 8:15AM to 12:45PM => [-45, 225], min meeting = 75 minutes.
# 6. Karen at Sunset District, available from 12:30PM to 1:00PM => [210, 240], min meeting = 15 minutes.
# 7. Patricia at Presidio, available from 3:00PM to 6:30PM => [360, 570], min meeting = 30 minutes.
# 8. Brian at Embarcadero, available from 6:45PM to 9:00PM => [585, 720], min meeting = 120 minutes.
# 9. Linda at Richmond District, available from 3:15PM to 4:15PM => [375, 435], min meeting = 15 minutes.
# 10. Paul at Bayview, available from 10:45AM to 5:45PM => [105, 525], min meeting = 75 minutes.
friends = [
    {"name": "Joseph",   "location": "Golden Gate Park",  "avail_start": 585, "avail_end": 690, "duration": 75},
    {"name": "Emily",    "location": "North Beach",       "avail_start": 345, "avail_end": 645, "duration": 105},
    {"name": "Jeffrey",  "location": "The Castro",        "avail_start": 450, "avail_end": 720, "duration": 120},
    {"name": "Sarah",    "location": "Russian Hill",      "avail_start": 525, "avail_end": 705, "duration": 45},
    {"name": "Jessica",  "location": "Nob Hill",          "avail_start": -45, "avail_end": 225, "duration": 75},
    {"name": "Karen",    "location": "Sunset District",   "avail_start": 210, "avail_end": 240, "duration": 15},
    {"name": "Patricia", "location": "Presidio",          "avail_start": 360, "avail_end": 570, "duration": 30},
    {"name": "Brian",    "location": "Embarcadero",       "avail_start": 585, "avail_end": 720, "duration": 120},
    {"name": "Linda",    "location": "Richmond District", "avail_start": 375, "avail_end": 435, "duration": 15},
    {"name": "Paul",     "location": "Bayview",           "avail_start": 105, "avail_end": 525, "duration": 75},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Marina District",
    "Golden Gate Park",
    "North Beach",
    "The Castro",
    "Russian Hill",
    "Nob Hill",
    "Sunset District",
    "Presidio",
    "Embarcadero",
    "Richmond District",
    "Bayview",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes)
# Note: travel times are not necessarily symmetric.
travel = {
    # From Marina District:
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Bayview"): 27,

    # From Golden Gate Park:
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Bayview"): 23,

    # From North Beach:
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Bayview"): 25,

    # From The Castro:
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Bayview"): 19,

    # From Russian Hill:
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Bayview"): 23,

    # From Nob Hill:
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Bayview"): 19,

    # From Sunset District:
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Bayview"): 22,

    # From Presidio:
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Bayview"): 31,

    # From Embarcadero:
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Bayview"): 21,

    # From Richmond District:
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Bayview"): 27,

    # From Bayview:
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
}

# Helper function to obtain travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use the Optimize() solver to maximize the total number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i, x[i] is a Boolean indicating if the meeting is scheduled,
# and start[i] is the meeting start time (in minutes relative to 9:00AM at Marina District).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Marina District at time 0.
arrival_location = "Marina District"
arrival_time = 0

# For each friend scheduled, impose:
#   - meeting starts no earlier than the available start time,
#   - meeting (plus duration) finishes by the available end time,
#   - and the meeting's start time respects the travel time from your arrival location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Add pairwise non-overlap constraints.
# For any two meetings i and j that are scheduled, ensure that either:
# meeting i (plus its duration and travel time from location i to j) finishes before meeting j starts,
# OR meeting j (plus its duration and travel time from location j to i) finishes before meeting i starts.
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

# Objective: maximize the sum of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve the scheduling problem and print the chosen itinerary.
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
            # Convert minutes relative to 9:00AM to HH:MM (9:00AM is 540 minutes after midnight).
            total = 540 + minutes
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")