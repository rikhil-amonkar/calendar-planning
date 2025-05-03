from z3 import *

# ---------------------------
# Data definitions
# ---------------------------
# We measure time in minutes after 9:00AM.
# Friend meeting data: each friend is given as:
#   name, location, available start, available end, and minimum meeting duration.
# Note: Times are expressed in minutes after 9:00AM.
#
# Starting location: Pacific Heights at 9:00AM.
#
# Conversions:
# Charles: Russian Hill from 11:30AM (150) to 5:30PM (510), duration 45.
# Amanda: Financial District from 1:00PM (240) to 4:00PM (420), duration 45.
# John: The Castro from 11:30AM (150) to 3:15PM (375), duration 45.
# Deborah: Alamo Square from 5:00PM (480) to 6:45PM (585), duration 90.
# Jessica: Presidio from 5:15PM (495) to 8:15PM (675), duration 105.
# Melissa: Mission District from 12:15PM (195) to 6:30PM (570), duration 90.
# Stephanie: Golden Gate Park from 4:00PM (420) to 8:15PM (675), duration 15.
# Steven: Marina District from 7:30PM (630) to 8:15PM (675), duration 30.
# George: Bayview from 9:45AM (45) to 9:00PM (720), duration 45.
# Mary: Embarcadero from 7:00PM (600) to 8:00PM (660), duration 30.

friends = [
    {"name": "Charles",   "location": "Russian Hill",      "avail_start": 150, "avail_end": 510, "duration": 45},
    {"name": "Amanda",    "location": "Financial District","avail_start": 240, "avail_end": 420, "duration": 45},
    {"name": "John",      "location": "The Castro",        "avail_start": 150, "avail_end": 375, "duration": 45},
    {"name": "Deborah",   "location": "Alamo Square",      "avail_start": 480, "avail_end": 585, "duration": 90},
    {"name": "Jessica",   "location": "Presidio",          "avail_start": 495, "avail_end": 675, "duration": 105},
    {"name": "Melissa",   "location": "Mission District",  "avail_start": 195, "avail_end": 570, "duration": 90},
    {"name": "Stephanie", "location": "Golden Gate Park",  "avail_start": 420, "avail_end": 675, "duration": 15},
    {"name": "Steven",    "location": "Marina District",   "avail_start": 630, "avail_end": 675, "duration": 30},
    {"name": "George",    "location": "Bayview",           "avail_start": 45,  "avail_end": 720, "duration": 45},
    {"name": "Mary",      "location": "Embarcadero",       "avail_start": 600, "avail_end": 660, "duration": 30},
]

# List of all locations (covering both starting location and friends’ meeting spots).
locations = [
    "Pacific Heights", "Russian Hill", "Financial District", "The Castro",
    "Alamo Square", "Presidio", "Mission District", "Golden Gate Park",
    "Marina District", "Bayview", "Embarcadero"
]

# Travel times (in minutes) between locations.
# Data is given as (origin, destination): travel time.
travel = {
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Embarcadero"): 10,

    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Embarcadero"): 8,

    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Embarcadero"): 4,

    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Embarcadero"): 22,

    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Embarcadero"): 16,

    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Embarcadero"): 20,

    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Embarcadero"): 19,

    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,

    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Embarcadero"): 14,

    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Embarcadero"): 19,

    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
}

def get_travel_time(origin, destination):
    # Returns travel time from origin to destination; we assume the key exists.
    return travel[(origin, destination)]

# -----------------------------
# Z3 Model
# -----------------------------
# We use Optimize to maximize the total number of meetings scheduled.
opt = Optimize()

num_friends = len(friends)

# Decision variables:
# x[i] is a Boolean indicating if we schedule meeting with friend i.
# start[i] is an integer representing the meeting’s start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -100, start[i] <= 1000)

# Starting location and arrival time.
# You arrive at Pacific Heights at 9:00AM, i.e. time 0.
start_location = "Pacific Heights"
arrival_time = 0

# For each friend, if scheduled then enforce:
#   (a) Meeting cannot start before the friend’s availability.
#   (b) Meeting (start + duration) must finish by friend’s available end time.
#   (c) Meeting start must be no earlier than the time needed to travel from the starting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    # travel time from starting location (Pacific Heights) to the friend’s meeting location
    travel_from_start = get_travel_time(start_location, loc)
    
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Non-overlap constraints:
# For any two scheduled meetings, enforce that either meeting i (including its duration and travel to j)
# finishes before meeting j starts OR vice versa.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        # Either meeting i (with travel time to j) is finished before meeting j starts
        # or meeting j (with travel time to i) is finished before meeting i starts.
        no_overlap = Or(start[i] + dur_i + travel_i_j <= start[j],
                        start[j] + dur_j + travel_j_i <= start[i])
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: Maximize the total number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------
# Solve and Display the Schedule
# -----------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            st = model.evaluate(start[i]).as_long()
            schedule.append((st, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for st, name, loc, dur in schedule:
        finish = st + dur
        def to_time(minutes):
            total = 9 * 60 + minutes
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc}: from {to_time(st)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")