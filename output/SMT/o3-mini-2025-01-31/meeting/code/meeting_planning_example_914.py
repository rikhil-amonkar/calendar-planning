from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
#
# All times are in minutes relative to 9:00AM.
#
# 1. Barbara at Nob Hill from 2:30PM to 8:45PM; meeting >= 75 minutes.
#    2:30PM = 330, 8:45PM = 705.
# 2. Elizabeth at Russian Hill from 12:15PM to 3:30PM; meeting >= 75 minutes.
#    12:15PM = 195, 3:30PM = 390.
# 3. Jason at Presidio from 10:00AM to 12:15PM; meeting >= 15 minutes.
#    10:00AM = 60, 12:15PM = 195.
# 4. Deborah at Financial District from 9:30PM to 10:30PM; meeting >= 60 minutes.
#    9:30PM = 750, 10:30PM = 810.
# 5. Charles at Union Square from 9:30AM to 3:15PM; meeting >= 120 minutes.
#    9:30AM = 30, 3:15PM = 375.
# 6. Sandra at Haight-Ashbury from 12:45PM to 4:00PM; meeting >= 90 minutes.
#    12:45PM = 195, 4:00PM = 420.
# 7. Patricia at Mission District from 7:30AM to 9:30PM; meeting >= 15 minutes.
#    7:30AM = -90, 9:30PM = 720.
# 8. George at Chinatown from 9:30AM to 1:45PM; meeting >= 75 minutes.
#    9:30AM = 30, 1:45PM = 285.
# 9. Joshua at Pacific Heights from 8:15AM to 3:15PM; meeting >= 60 minutes.
#    8:15AM = -45, 3:15PM = 375.
# 10. Jeffrey at Golden Gate Park from 4:45PM to 6:45PM; meeting >= 75 minutes.
#     4:45PM = 435, 6:45PM = 585.
friends = [
    {"name": "Barbara",   "location": "Nob Hill",           "avail_start": 330, "avail_end": 705, "duration": 75},
    {"name": "Elizabeth", "location": "Russian Hill",       "avail_start": 195, "avail_end": 390, "duration": 75},
    {"name": "Jason",     "location": "Presidio",           "avail_start": 60,  "avail_end": 195, "duration": 15},
    {"name": "Deborah",   "location": "Financial District", "avail_start": 750, "avail_end": 810, "duration": 60},
    {"name": "Charles",   "location": "Union Square",       "avail_start": 30,  "avail_end": 375, "duration": 120},
    {"name": "Sandra",    "location": "Haight-Ashbury",     "avail_start": 195, "avail_end": 420, "duration": 90},
    {"name": "Patricia",  "location": "Mission District",   "avail_start": -90, "avail_end": 720, "duration": 15},
    {"name": "George",    "location": "Chinatown",          "avail_start": 30,  "avail_end": 285, "duration": 75},
    {"name": "Joshua",    "location": "Pacific Heights",    "avail_start": -45, "avail_end": 375, "duration": 60},
    {"name": "Jeffrey",   "location": "Golden Gate Park",   "avail_start": 435, "avail_end": 585, "duration": 75},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Embarcadero",
    "Nob Hill",
    "Russian Hill",
    "Presidio",
    "Financial District",
    "Union Square",
    "Haight-Ashbury",
    "Mission District",
    "Chinatown",
    "Pacific Heights",
    "Golden Gate Park",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# The keys are tuples (origin, destination). Data provided below.
travel = {
    # From Embarcadero:
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Golden Gate Park"): 25,
    
    # From Nob Hill:
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    
    # From Russian Hill:
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Union Square"): 13,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    
    # From Presidio:
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    
    # From Financial District:
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    
    # From Union Square:
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    
    # From Mission District:
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    
    # From Chinatown:
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    
    # From Pacific Heights:
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i:
#   x[i] is a Boolean that is True if we schedule a meeting with friend i.
#   start[i] is the meeting start time (in minutes relative to 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location: Embarcadero at 9:00AM (time = 0)
starting_location = "Embarcadero"
arrival_time = 0

# For each scheduled friend, enforce:
# 1. Meeting start must be no earlier than the friend’s available start.
# 2. Meeting plus its duration must finish by the friend’s available end.
# 3. There is enough time to get from the starting location.
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
# For every pair of scheduled meetings, ensure that one meeting (plus the travel time to the next)
# finishes before the other begins.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        # Either meeting i finishes and then travel to j, or meeting j finishes and then travel to i.
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