from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# All times are measured in minutes relative to your arrival at Haight-Ashbury at 9:00AM (time = 0).
# For each friend, we define:
#   - location
#   - available window (avail_start, avail_end)
#   - minimum meeting duration
#
# Times have been converted as follows:
# James: at Bayview, from 11:15AM to 4:30PM  -> [135, 450], meeting duration >= 60 minutes.
# Nancy: at Richmond District, from 9:30PM to 10:00PM -> [750, 780], meeting duration >= 30 minutes.
# Carol: at Financial District, from 10:30AM to 6:30PM -> [90, 570], meeting duration >= 15 minutes.
# Sandra: at Alamo Square, from 7:00PM to 8:30PM -> [600, 690], meeting duration >= 45 minutes.
# Joshua: at Fisherman's Wharf, from 9:15PM to 10:15PM -> [735, 795], meeting duration >= 60 minutes.
# Karen: at Presidio, from 3:15PM to 10:00PM -> [375, 780], meeting duration >= 90 minutes.
# Matthew: at Russian Hill, from 6:00PM to 8:15PM -> [540, 675], meeting duration >= 90 minutes.
# Brian: at Golden Gate Park, from 10:30AM to 6:45PM -> [90, 585], meeting duration >= 120 minutes.
# Helen: at The Castro, from 5:00PM to 7:15PM -> [480, 615], meeting duration >= 120 minutes.
# Timothy: at Union Square, from 7:15AM to 8:30PM -> avail_start = 7:15AM is -105 minutes, avail_end = 8:30PM is 690 minutes; meeting duration >= 120 minutes.
friends = [
    {"name": "James",    "location": "Bayview",           "avail_start": 135, "avail_end": 450, "duration": 60},
    {"name": "Nancy",    "location": "Richmond District", "avail_start": 750, "avail_end": 780, "duration": 30},
    {"name": "Carol",    "location": "Financial District","avail_start": 90,  "avail_end": 570, "duration": 15},
    {"name": "Sandra",   "location": "Alamo Square",      "avail_start": 600, "avail_end": 690, "duration": 45},
    {"name": "Joshua",   "location": "Fisherman's Wharf", "avail_start": 735, "avail_end": 795, "duration": 60},
    {"name": "Karen",    "location": "Presidio",          "avail_start": 375, "avail_end": 780, "duration": 90},
    {"name": "Matthew",  "location": "Russian Hill",      "avail_start": 540, "avail_end": 675, "duration": 90},
    {"name": "Brian",    "location": "Golden Gate Park",  "avail_start": 90,  "avail_end": 585, "duration": 120},
    {"name": "Helen",    "location": "The Castro",        "avail_start": 480, "avail_end": 615, "duration": 120},
    {"name": "Timothy",  "location": "Union Square",      "avail_start": -105,"avail_end": 690, "duration": 120},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Haight-Ashbury",
    "Bayview",
    "Richmond District",
    "Financial District",
    "Alamo Square",
    "Fisherman's Wharf",
    "Presidio",
    "Russian Hill",
    "Golden Gate Park",
    "The Castro",
    "Union Square",
]

# -----------------------------------------------------------------------------
# Travel distances between locations (in minutes).
# Each tuple (origin, destination) maps to the travel time in minutes.
travel = {
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    
    # From Bayview:
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Union Square"): 18,
    
    # From Richmond District:
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Union Square"): 21,
    
    # From Financial District:
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 23,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Union Square"): 9,
    
    # From Alamo Square:
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Union Square"): 14,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Union Square"): 13,
    
    # From Presidio:
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Union Square"): 22,
    
    # From Russian Hill:
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Union Square"): 10,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Union Square"): 22,
    
    # From The Castro:
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Union Square"): 19,
    
    # From Union Square:
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "The Castro"): 17,
}

# Helper function to obtain travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 Model and Optimization.
# -----------------------------------------------------------------------------
# Create an Optimize() instance to maximize the number of scheduled meetings.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i] is a Boolean that indicates whether to schedule a meeting with friend i.
# start[i] is the integer start time (in minutes after 9:00AM) for the meeting with friend i.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Haight-Ashbury at 9:00AM (time 0).
arrival_location = "Haight-Ashbury"
arrival_time = 0

# For each scheduled meeting, enforce:
#   1. The meeting occurs within the friend’s available window.
#   2. The meeting’s end time (start + duration) is within the available window.
#   3. You can only begin the meeting after arriving at the destination from Haight-Ashbury.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Add pairwise non-overlap constraints.
# If two meetings are scheduled, ensure that after accounting for meeting duration and travel time from one friend’s location to the next, the meetings do not overlap.
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

# -----------------------------------------------------------------------------
# Solve and output the optimal itinerary.
# -----------------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda t: t[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Haight-Ashbury):")
    for s_time, name, loc, dur in schedule:
        end_time = s_time + dur
        def to_time(m):
            # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) into HH:MM format.
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(s_time)} to {to_time(end_time)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")