from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# Times are expressed in minutes relative to your arrival at Bayview at 9:00AM (time = 0).

# 1. Thomas at Golden Gate Park from 7:30PM to 10:00PM => [630, 780], minimum meeting = 120 minutes.
# 2. George at Alamo Square from 7:15AM to 5:15PM => [ -45, 495], minimum meeting = 45 minutes.
# 3. Laura at Fisherman's Wharf from 3:15PM to 9:00PM => [ 375, 720], minimum meeting = 75 minutes.
# 4. Emily at Nob Hill from 9:30PM to 10:30PM => [750, 810], minimum meeting = 60 minutes.
# 5. Kimberly at Presidio from 3:15PM to 8:15PM => [375, 675], minimum meeting = 120 minutes.
# 6. Patricia at Financial District from 3:45PM to 7:45PM => [405, 645], minimum meeting = 120 minutes.
# 7. Amanda at Sunset District from 7:15PM to 9:00PM => [630, 720], minimum meeting = 60 minutes.
# 8. Mark at Marina District from 5:30PM to 9:00PM => [510, 720], minimum meeting = 75 minutes.
# 9. Daniel at The Castro from 4:15PM to 9:15PM => [435, 735], minimum meeting = 15 minutes.
# 10. John at North Beach from 12:45PM to 7:30PM => [225, 630], minimum meeting = 60 minutes.
friends = [
    {"name": "Thomas",   "location": "Golden Gate Park",    "avail_start": 630, "avail_end": 780, "duration": 120},
    {"name": "George",   "location": "Alamo Square",        "avail_start": -45, "avail_end": 495, "duration": 45},
    {"name": "Laura",    "location": "Fisherman's Wharf",   "avail_start": 375, "avail_end": 720, "duration": 75},
    {"name": "Emily",    "location": "Nob Hill",            "avail_start": 750, "avail_end": 810, "duration": 60},
    {"name": "Kimberly", "location": "Presidio",            "avail_start": 375, "avail_end": 675, "duration": 120},
    {"name": "Patricia", "location": "Financial District",  "avail_start": 405, "avail_end": 645, "duration": 120},
    {"name": "Amanda",   "location": "Sunset District",     "avail_start": 630, "avail_end": 720, "duration": 60},
    {"name": "Mark",     "location": "Marina District",     "avail_start": 510, "avail_end": 720, "duration": 75},
    {"name": "Daniel",   "location": "The Castro",          "avail_start": 435, "avail_end": 735, "duration": 15},
    {"name": "John",     "location": "North Beach",         "avail_start": 225, "avail_end": 630, "duration": 60},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Bayview",
    "Golden Gate Park",
    "Alamo Square",
    "Fisherman's Wharf",
    "Nob Hill",
    "Presidio",
    "Financial District",
    "Sunset District",
    "Marina District",
    "The Castro",
    "North Beach",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# These are taken from the problem statement.
travel = {
    # From Bayview:
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "North Beach"): 22,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "North Beach"): 23,
    
    # From Alamo Square:
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    
    # From Nob Hill:
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    
    # From Presidio:
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    
    # From Financial District:
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "North Beach"): 7,
    
    # From Sunset District:
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "North Beach"): 28,
    
    # From Marina District:
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "North Beach"): 11,
    
    # From The Castro:
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    
    # From North Beach:
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "The Castro"): 23,
}

# Helper function to get travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize() to maximize the number of friends met.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i] is True if we schedule a meeting with friend i.
# start[i] is the start time of the meeting (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Bayview at time 0.
arrival_location = "Bayview"
arrival_time = 0

# For each meeting that is scheduled, add constraints:
# 1. Meeting must start no earlier than available start.
# 2. Meeting plus its minimum duration must finish by the available end.
# 3. There must be enough time to travel from your arrival location to the meeting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Pairwise non-overlap constraints:
# For any two scheduled meetings i and j, ensure that one finishes (plus travel time to the next) before the other starts.
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
        if is_true(model.evaluate(x[i])):
            t_val = model.evaluate(start[i]).as_long()
            schedule.append((t_val, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM at Bayview):")
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