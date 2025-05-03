from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
#
# All times are in minutes relative to 9:00AM.
# The conversion is: RelativeTime = (Actual Time in minutes) – 540.
#
# 1. Karen at Alamo Square from 2:15PM to 8:15PM; meeting >= 45 minutes.
#    2:15PM -> 855-540 = 315, 8:15PM -> 1215-540 = 675.
# 2. Carol at Financial District from 4:00PM to 6:15PM; meeting >= 60 minutes.
#    4:00PM -> 960-540 = 420, 6:15PM -> 1095-540 = 555.
# 3. Sarah at Pacific Heights from 11:15AM to 4:15PM; meeting >= 75 minutes.
#    11:15AM -> 675-540 = 135, 4:15PM -> 975-540 = 435.
# 4. Ashley at Richmond District from 11:45AM to 4:30PM; meeting >= 120 minutes.
#    11:45AM -> 705-540 = 165, 4:30PM -> 990-540 = 450.
# 5. Betty at Nob Hill from 8:45PM to 10:00PM; meeting >= 60 minutes.
#    8:45PM -> 1245-540 = 705, 10:00PM -> 1320-540 = 780.
# 6. Matthew at Russian Hill from 9:15PM to 10:15PM; meeting >= 45 minutes.
#    9:15PM -> 1275-540 = 735, 10:15PM -> 1335-540 = 795.
# 7. Mark at Presidio from 7:00PM to 8:30PM; meeting >= 30 minutes.
#    7:00PM -> 1140-540 = 600, 8:30PM -> 1230-540 = 690.
# 8. George at Sunset District from 10:00AM to 3:45PM; meeting >= 15 minutes.
#    10:00AM -> 600-540 = 60, 3:45PM -> 945-540 = 405.
# 9. Richard at Golden Gate Park from 12:30PM to 7:15PM; meeting >= 105 minutes.
#    12:30PM -> 750-540 = 210, 7:15PM -> 1155-540 = 615.
# 10. Timothy at Bayview from 12:45PM to 8:15PM; meeting >= 90 minutes.
#     12:45PM -> 765-540 = 225, 8:15PM -> 1215-540 = 675.
friends = [
    {"name": "Karen",    "location": "Alamo Square",     "avail_start": 315, "avail_end": 675, "duration": 45},
    {"name": "Carol",    "location": "Financial District", "avail_start": 420, "avail_end": 555, "duration": 60},
    {"name": "Sarah",    "location": "Pacific Heights",    "avail_start": 135, "avail_end": 435, "duration": 75},
    {"name": "Ashley",   "location": "Richmond District",  "avail_start": 165, "avail_end": 450, "duration": 120},
    {"name": "Betty",    "location": "Nob Hill",           "avail_start": 705, "avail_end": 780, "duration": 60},
    {"name": "Matthew",  "location": "Russian Hill",       "avail_start": 735, "avail_end": 795, "duration": 45},
    {"name": "Mark",     "location": "Presidio",           "avail_start": 600, "avail_end": 690, "duration": 30},
    {"name": "George",   "location": "Sunset District",    "avail_start": 60,  "avail_end": 405, "duration": 15},
    {"name": "Richard",  "location": "Golden Gate Park",   "avail_start": 210, "avail_end": 615, "duration": 105},
    {"name": "Timothy",  "location": "Bayview",            "avail_start": 225, "avail_end": 675, "duration": 90},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Marina District",
    "Alamo Square",
    "Financial District",
    "Pacific Heights",
    "Richmond District",
    "Nob Hill",
    "Russian Hill",
    "Presidio",
    "Sunset District",
    "Golden Gate Park",
    "Bayview",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# Data as provided.
travel = {
    # From Marina District:
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Bayview"): 27,
    
    # From Alamo Square:
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,
    
    # From Financial District:
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,
    
    # From Pacific Heights:
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Bayview"): 22,
    
    # From Richmond District:
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,
    
    # From Nob Hill:
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Bayview"): 19,
    
    # From Russian Hill:
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Bayview"): 23,
    
    # From Presidio:
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    
    # From Sunset District:
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Bayview"): 23,
    
    # From Bayview:
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,
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
#   x[i] is True if meeting with friend i is scheduled.
#   start[i] is the meeting start time (in minutes relative to 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location: Marina District at 9:00AM (time = 0).
starting_location = "Marina District"
arrival_time = 0

# For each friend meeting scheduled, enforce:
# 1. Meeting cannot start before the friend’s available start.
# 2. The meeting (plus its required duration) must finish by the available end.
# 3. There is enough travel time from the starting location.
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
# For every pair of scheduled meetings, ensure that one meeting (plus travel time to the next)
# finishes before the other starts.
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

# Objective: maximize the number of meetings scheduled.
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
            total = 540 + minutes  # since 9:00AM is 540 minutes after midnight
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")