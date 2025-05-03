from z3 import *

# ---------------------------
# Data definitions
# ---------------------------

# We measure all times in minutes after 9:00AM.
# Friend meeting data: name, location, available start time,
# available end time, and required meeting duration.
# Note: Some avail_start times are before 9:00AM; this is acceptable because our constraints
# will force the meeting start to be no earlier than travel time from Russian Hill.
friends = [
    {"name": "Emily",    "location": "Pacific Heights",    "avail_start": 15,  "avail_end": 285, "duration": 120},  # 9:15AM to 1:45PM
    {"name": "Helen",    "location": "North Beach",        "avail_start": 285, "avail_end": 585, "duration": 30},   # 1:45PM to 6:45PM
    {"name": "Kimberly", "location": "Golden Gate Park",   "avail_start": 585, "avail_end": 735, "duration": 75},   # 6:45PM to 9:15PM
    {"name": "James",    "location": "Embarcadero",        "avail_start": 90,  "avail_end": 150, "duration": 30},   # 10:30AM to 11:30AM
    {"name": "Linda",    "location": "Haight-Ashbury",     "avail_start": -90, "avail_end": 615, "duration": 15},   # 7:30AM to 7:15PM
    {"name": "Paul",     "location": "Fisherman's Wharf",  "avail_start": 345, "avail_end": 585, "duration": 90},   # 2:45PM to 6:45PM
    {"name": "Anthony",  "location": "Mission District",   "avail_start": -60, "avail_end": 345, "duration": 105},  # 8:00AM to 2:45PM
    {"name": "Nancy",    "location": "Alamo Square",       "avail_start": -30, "avail_end": 285, "duration": 120},  # 8:30AM to 1:45PM
    {"name": "William",  "location": "Bayview",            "avail_start": 510, "avail_end": 690, "duration": 120},  # 5:30PM to 8:30PM
    {"name": "Margaret", "location": "Richmond District",  "avail_start": 375, "avail_end": 555, "duration": 45}    # 3:15PM to 6:15PM
]

# List all locations.
locations = ["Russian Hill", "Pacific Heights", "North Beach", "Golden Gate Park",
             "Embarcadero", "Haight-Ashbury", "Fisherman's Wharf", "Mission District",
             "Alamo Square", "Bayview", "Richmond District"]

# Travel times between locations (in minutes)
# Provided data follows the given table. We include all pairs as key: (origin, destination)
travel = {
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Richmond District"): 14,

    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Richmond District"): 12,

    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Richmond District"): 18,

    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Richmond District"): 7,

    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,

    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Richmond District"): 10,

    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Richmond District"): 18,

    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Richmond District"): 20,

    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Richmond District"): 11,

    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Richmond District"): 27,

    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,
}

def get_travel_time(orig, dest):
    # Assumes the key exists in the dictionary.
    return travel[(orig, dest)]

# -----------------------------
# Z3 Model
# -----------------------------

# Use an optimizer so we can maximize the number of meetings scheduled.
opt = Optimize()

n = len(friends)

# Decision variables:
# For each friend i, x[i] is a Bool that is True if we schedule that meeting.
# start[i] is the start time (in minutes after 9:00AM) at which we begin the meeting.
x = [Bool(f"x_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]

# Allow a wide range for meeting start times.
for i in range(n):
    opt.add(start[i] >= -100, start[i] <= 1000)

# Starting location is Russian Hill at time 0.
start_location = "Russian Hill"
arrival_time = 0

# For each friend, if the meeting is scheduled then:
#   (a) It must start no earlier than the friend’s available start time.
#   (b) The meeting must end (start + duration) no later than the friend’s available end time.
#   (c) It must start no earlier than the time required to travel from the starting point (Russian Hill) to that friend.
for i, f in enumerate(friends):
    dur = f["duration"]
    availS = f["avail_start"]
    availE = f["avail_end"]
    loc = f["location"]
    travel_from_start = get_travel_time(start_location, loc)
    opt.add(Implies(x[i], start[i] >= availS))
    opt.add(Implies(x[i], start[i] + dur <= availE))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Add nonoverlap constraints for every pair of meetings if both are scheduled.
# That is, for any two meetings i and j, one must finish (including travel time from i to j)
# before the other starts.
for i in range(n):
    for j in range(i+1, n):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        # Either i comes before j, or j comes before i:
        cond = Or(start[i] + dur_i + travel_i_j <= start[j],
                  start[j] + dur_j + travel_j_i <= start[i])
        opt.add(Implies(And(x[i], x[j]), cond))

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(n)]))

# -----------------------------
# Solve the model
# -----------------------------

if opt.check() == sat:
    m = opt.model()
    scheduled = []
    for i in range(n):
        if m.evaluate(x[i]):
            st = m.evaluate(start[i]).as_long()
            scheduled.append((st, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    scheduled.sort(key=lambda t: t[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for st, name, loc, dur in scheduled:
        finish = st + dur
        def to_time(minutes):
            # Adjust negative minutes appropriately (if meeting window started before 9:00AM)
            total = 9*60 + minutes
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc}: from {to_time(st)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")