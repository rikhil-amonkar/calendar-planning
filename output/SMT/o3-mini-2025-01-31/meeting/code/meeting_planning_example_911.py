from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
#
# Times are measured in minutes relative to 9:00AM (time 0).
#
# Available windows (after converting start time relative to 9:00AM):
#
# Steven at North Beach from 5:30PM to 8:30PM:
#   5:30PM = 510 minutes; 8:30PM = 690 minutes. Minimum meeting duration: 15
#
# Sarah at Golden Gate Park from 5:00PM to 7:15PM:
#   5:00PM = 480 minutes; 7:15PM = 615 minutes. Minimum meeting duration: 75
#
# Brian at Embarcadero from 2:15PM to 4:00PM:
#   2:15PM = 315 minutes; 4:00PM = 420 minutes. Minimum meeting duration: 105
#
# Stephanie at Haight-Ashbury from 10:15AM to 12:15PM:
#   10:15AM = 75 minutes; 12:15PM = 195 minutes. Minimum meeting duration: 75
#
# Melissa at Richmond District from 2:00PM to 7:30PM:
#   2:00PM = 300 minutes; 7:30PM = 630 minutes. Minimum meeting duration: 30
#
# Nancy at Nob Hill from 8:15AM to 12:45PM:
#   8:15AM = -45 minutes; 12:45PM = 225 minutes. Minimum meeting duration: 90
#
# David at Marina District from 11:15AM to 1:15PM:
#   11:15AM = 135 minutes; 1:15PM = 255 minutes. Minimum meeting duration: 120
#
# James at Presidio from 3:00PM to 6:15PM:
#   3:00PM = 360 minutes; 6:15PM = 555 minutes. Minimum meeting duration: 120
#
# Elizabeth at Union Square from 11:30AM to 9:00PM:
#   11:30AM = 150 minutes; 9:00PM = 720 minutes. Minimum meeting duration: 60
#
# Robert at Financial District from 1:15PM to 3:15PM:
#   1:15PM = 255 minutes; 3:15PM = 375 minutes. Minimum meeting duration: 45

friends = [
    {"name": "Steven",    "location": "North Beach",         "avail_start": 510, "avail_end": 690, "duration": 15},
    {"name": "Sarah",     "location": "Golden Gate Park",    "avail_start": 480, "avail_end": 615, "duration": 75},
    {"name": "Brian",     "location": "Embarcadero",         "avail_start": 315, "avail_end": 420, "duration": 105},
    {"name": "Stephanie", "location": "Haight-Ashbury",      "avail_start": 75,  "avail_end": 195, "duration": 75},
    {"name": "Melissa",   "location": "Richmond District",   "avail_start": 300, "avail_end": 630, "duration": 30},
    {"name": "Nancy",     "location": "Nob Hill",            "avail_start": -45, "avail_end": 225, "duration": 90},
    {"name": "David",     "location": "Marina District",     "avail_start": 135, "avail_end": 255, "duration": 120},
    {"name": "James",     "location": "Presidio",            "avail_start": 360, "avail_end": 555, "duration": 120},
    {"name": "Elizabeth", "location": "Union Square",        "avail_start": 150, "avail_end": 720, "duration": 60},
    {"name": "Robert",    "location": "Financial District",  "avail_start": 255, "avail_end": 375, "duration": 45},
]

# ---------------------------------------------------------------------
# List of locations (includes all meeting places plus the starting point).
locations = [
    "The Castro",
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Richmond District",
    "Nob Hill",
    "Marina District",
    "Presidio",
    "Union Square",
    "Financial District",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# Keys are tuples (origin, destination)
travel = {
    # From The Castro:
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
    
    # From North Beach:
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
    
    # From Golden Gate Park:
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
    
    # From Embarcadero:
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Financial District"): 5,
    
    # From Haight-Ashbury:
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
    
    # From Richmond District:
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
    
    # From Nob Hill:
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
    
    # From Marina District:
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
    
    # From Presidio:
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
    
    # From Union Square:
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
    
    # From Financial District:
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

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model
# ---------------------------------------------------------------------
# Use Optimize to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i] = True if meeting with friend i is scheduled.
#   start[i] = meeting start time in minutes (relative to 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set some broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location is The Castro at 9:00AM (time 0).
starting_location = "The Castro"
arrival_time = 0

# For each friend scheduled, enforce:
# (a) The meeting cannot start before the friend’s available start.
# (b) The meeting must finish by the friend’s available end.
# (c) There must be enough travel time from the starting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(starting_location, loc)
    
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Non-overlap constraints:
# For every pair of scheduled meetings, ensure that one meeting (plus the travel time)
# finishes before the other begins.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_to_j = get_travel_time(loc_i, loc_j)
        travel_j_to_i = get_travel_time(loc_j, loc_i)
        no_overlap = Or(
            start[i] + dur_i + travel_i_to_j <= start[j],
            start[j] + dur_j + travel_j_to_i <= start[i]
        )
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and output the schedule.
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            t = model.evaluate(start[i]).as_long()
            schedule.append((t, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            total = 9 * 60 + minutes
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")