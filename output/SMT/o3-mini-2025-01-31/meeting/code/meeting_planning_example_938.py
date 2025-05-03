from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are in minutes relative to 9:00AM at Haight-Ashbury (time = 0).
# Convert the provided clock times as follows:
# Amanda (Nob Hill): 8:45AM to 3:30PM  --> avail: [-15, 390], duration >= 45 minutes.
# Joseph (Bayview): 9:30AM to 10:30AM   --> avail: [30, 90], duration >= 45 minutes.
# Lisa (Fisherman's Wharf): 9:00PM to 10:00PM  --> avail: [720, 780], duration >= 60 minutes.
# Andrew (Richmond District): 6:00PM to 7:30PM --> avail: [540, 630], duration >= 15 minutes.
# Jason (Union Square): 4:15PM to 8:15PM  --> avail: [435, 675], duration >= 90 minutes.
# James (Sunset District): 8:00PM to 10:00PM  --> avail: [660, 780], duration >= 120 minutes.
# Paul (Mission District): 10:45AM to 9:30PM  --> avail: [105, 750], duration >= 105 minutes.
# Ronald (Russian Hill): 6:00PM to 7:15PM --> avail: [540, 615], duration >= 30 minutes.
# Thomas (Alamo Square): 3:15PM to 9:45PM  --> avail: [375, 765], duration >= 30 minutes.
# Melissa (Presidio): 3:00PM to 8:45PM  --> avail: [360, 705], duration >= 105 minutes.
friends = [
    {"name": "Amanda",   "location": "Nob Hill",            "avail_start": -15, "avail_end": 390, "duration": 45},
    {"name": "Joseph",   "location": "Bayview",             "avail_start": 30,  "avail_end": 90,  "duration": 45},
    {"name": "Lisa",     "location": "Fisherman's Wharf",   "avail_start": 720, "avail_end": 780, "duration": 60},
    {"name": "Andrew",   "location": "Richmond District",   "avail_start": 540, "avail_end": 630, "duration": 15},
    {"name": "Jason",    "location": "Union Square",        "avail_start": 435, "avail_end": 675, "duration": 90},
    {"name": "James",    "location": "Sunset District",     "avail_start": 660, "avail_end": 780, "duration": 120},
    {"name": "Paul",     "location": "Mission District",    "avail_start": 105, "avail_end": 750, "duration": 105},
    {"name": "Ronald",   "location": "Russian Hill",        "avail_start": 540, "avail_end": 615, "duration": 30},
    {"name": "Thomas",   "location": "Alamo Square",        "avail_start": 375, "avail_end": 765, "duration": 30},
    {"name": "Melissa",  "location": "Presidio",            "avail_start": 360, "avail_end": 705, "duration": 105},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Haight-Ashbury",       # Arrival point at 9:00AM.
    "Nob Hill",
    "Bayview",
    "Fisherman's Wharf",
    "Richmond District",
    "Union Square",
    "Sunset District",
    "Mission District",
    "Russian Hill",
    "Alamo Square",
    "Presidio",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# These are directional.
travel = {
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Presidio"): 15,

    # From Nob Hill:
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,

    # From Bayview:
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Presidio"): 32,

    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Presidio"): 17,

    # From Richmond District:
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Presidio"): 7,

    # From Union Square:
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,

    # From Sunset District:
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Presidio"): 16,

    # From Mission District:
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Presidio"): 25,

    # From Russian Hill:
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,

    # From Alamo Square:
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 17,

    # From Presidio:
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Alamo Square"): 19,
}

# Helper function to get travel time from an origin to a destination.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i] is a Boolean indicating whether we schedule a meeting with friend i.
#   start[i] is an integer giving the start time of the meeting (minutes from 9:00AM at Haight-Ashbury).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Haight-Ashbury at time = 0.
arrival_location = "Haight-Ashbury"
arrival_time = 0

# For each friend, if the meeting is scheduled then:
# - It must start no earlier than the friend's available start.
# - The meeting (start + duration) must finish before the friend's available end.
# - Additionally, you must have enough time to travel from your starting location (Haight-Ashbury).
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
# For any two scheduled meetings, ensure that after finishing one meeting and traveling to the next friend's location,
# the next meeting does not start until after that travel is complete.
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

# Objective: maximize the number of meetings scheduled.
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
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Haight-Ashbury):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        # Helper to convert minutes after 9:00AM into HH:MM (assuming 9:00AM is 540 minutes after midnight).
        def format_time(m):
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")