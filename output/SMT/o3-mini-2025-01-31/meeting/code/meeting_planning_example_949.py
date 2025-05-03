from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Sunset District:
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Haight-Ashbury"): 15,
    
    # From Richmond District:
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Haight-Ashbury"): 10,
    
    # From Mission District:
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Haight-Ashbury"): 12,
    
    # From Russian Hill:
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Haight-Ashbury"): 17,
    
    # From North Beach:
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Haight-Ashbury"): 18,
    
    # From Bayview:
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Haight-Ashbury"): 19,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    
    # From Alamo Square:
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Haight-Ashbury"): 5,
    
    # From The Castro:
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    
    # From Nob Hill:
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimization model.
opt = Optimize()

# Our arrival point is Sunset District at 9:00AM, so time = 0.
arrival_location = "Sunset District"
arrival_time = 0

# Define friend meeting constraints.
# Times are expressed as minutes after 9:00AM.
# Andrew: at Richmond District from 3:15PM to 6:30PM -> 3:15PM = 375, 6:30PM = 570, duration = 60.
# Kimberly: at Mission District from 10:15AM to 7:45PM -> 10:15AM = 75, 7:45PM = 645, duration = 60.
# Betty: at Russian Hill from 3:00PM to 9:00PM -> 3:00PM = 360, 9:00PM = 720, duration = 45.
# George: at North Beach from 11:00AM to 4:45PM -> 11:00AM = 120, 4:45PM = 465, duration = 75.
# Ashley: at Bayview from 12:30PM to 4:30PM -> 12:30PM = 210, 4:30PM = 450, duration = 45.
# Anthony: at Golden Gate Park from 7:30PM to 9:00PM -> 7:30PM = 630, 9:00PM = 720, duration = 90.
# Ronald: at Alamo Square from 6:45PM to 10:00PM -> 6:45PM = 585, 10:00PM = 780, duration = 75.
# Melissa: at The Castro from 9:45AM to 5:30PM -> 9:45AM = 45, 5:30PM = 510, duration = 75.
# Karen: at Nob Hill from 10:30AM to 4:00PM -> 10:30AM = 90, 4:00PM = 420, duration = 120.
# Joshua: at Haight-Ashbury from 7:30PM to 9:30PM -> 7:30PM = 630, 9:30PM = 750, duration = 75.
friends = [
    {"name": "Andrew",    "location": "Richmond District",  "avail_start": 375, "avail_end": 570, "duration": 60},
    {"name": "Kimberly",  "location": "Mission District",   "avail_start": 75,  "avail_end": 645, "duration": 60},
    {"name": "Betty",     "location": "Russian Hill",       "avail_start": 360, "avail_end": 720, "duration": 45},
    {"name": "George",    "location": "North Beach",        "avail_start": 120, "avail_end": 465, "duration": 75},
    {"name": "Ashley",    "location": "Bayview",            "avail_start": 210, "avail_end": 450, "duration": 45},
    {"name": "Anthony",   "location": "Golden Gate Park",   "avail_start": 630, "avail_end": 720, "duration": 90},
    {"name": "Ronald",    "location": "Alamo Square",       "avail_start": 585, "avail_end": 780, "duration": 75},
    {"name": "Melissa",   "location": "The Castro",         "avail_start": 45,  "avail_end": 510, "duration": 75},
    {"name": "Karen",     "location": "Nob Hill",           "avail_start": 90,  "avail_end": 420, "duration": 120},
    {"name": "Joshua",    "location": "Haight-Ashbury",     "avail_start": 630, "avail_end": 750, "duration": 75},
]

num_friends = len(friends)

# List of all relevant locations.
locations = [
    "Sunset District",
    "Richmond District",
    "Mission District",
    "Russian Hill",
    "North Beach",
    "Bayview",
    "Golden Gate Park",
    "Alamo Square",
    "The Castro",
    "Nob Hill",
    "Haight-Ashbury",
]

# Decision variables:
# For each friend i:
#   x[i]: a Boolean indicating whether the meeting is scheduled.
#   start[i]: an integer representing the start time (in minutes after 9:00AM) of the meeting.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Use a broad domain for the meeting start times.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For every scheduled meeting, ensure:
# - The meeting starts no earlier than the friend’s available start.
# - The meeting (start + duration) ends by the friend’s available end.
# - There is enough time to travel from our arrival (Sunset District) to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For every pair of scheduled meetings, add non-overlap constraints so that meetings do not conflict.
# Between any two meetings i and j, either meeting i (plus its duration and travel time from i to j)
# must finish before meeting j starts, or vice versa.
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

# Set the objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    # Sort scheduled meetings by start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM):")
    def format_time(m):
        # Convert minutes after 9:00AM to a HH:MM string (given that 9:00AM equals 540 minutes after midnight).
        total = 540 + m
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")