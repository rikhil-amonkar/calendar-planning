from z3 import *

# ---------------------------
# Data definitions
# ---------------------------
# All times are measured in minutes after 9:00AM.
# Note: times earlier than 9:00AM are negative.
#
# Friends meeting definitions:
# 1. Steven: at Fisherman's Wharf from 8:45AM to 11:00AM.
#    8:45AM = -15, 11:00AM = 120.  Minimum meeting = 75 minutes.
# 2. Rebecca: at Mission District from 9:45AM to 11:45AM.
#    9:45AM = 45, 11:45AM = 165.  Minimum meeting = 15 minutes.
# 3. Robert: at Richmond District from 6:15PM to 6:45PM.
#    6:15PM = 555, 6:45PM = 585.  Minimum meeting = 30 minutes.
# 4. James: at Financial District from 7:45PM to 9:00PM.
#    7:45PM = 645, 9:00PM = 720.  Minimum meeting = 15 minutes.
# 5. Sandra: at Marina District from 2:15PM to 5:00PM.
#    2:15PM = 375, 5:00PM = 480.  Minimum meeting = 75 minutes.
# 6. Charles: at Sunset District from 11:00AM to 4:00PM.
#    11:00AM = 120, 4:00PM = 420.  Minimum meeting = 60 minutes.
# 7. Carol: at Embarcadero from 7:00PM to 9:30PM.
#    7:00PM = 600, 9:30PM = 750.  Minimum meeting = 90 minutes.
# 8. Helen: at Presidio from 12:30PM to 2:30PM.
#    12:30PM = 210, 2:30PM = 330.  Minimum meeting = 15 minutes.
# 9. Karen: at Union Square from 7:00PM to 9:15PM.
#    7:00PM = 600, 9:15PM = 735.  Minimum meeting = 60 minutes.
# 10. John: at Russian Hill from 1:00PM to 5:15PM.
#    1:00PM = 240, 5:15PM = 495.  Minimum meeting = 90 minutes.

friends = [
    {"name": "Steven",   "location": "Fisherman's Wharf", "avail_start": -15, "avail_end": 120, "duration": 75},
    {"name": "Rebecca",  "location": "Mission District",  "avail_start": 45,  "avail_end": 165, "duration": 15},
    {"name": "Robert",   "location": "Richmond District", "avail_start": 555, "avail_end": 585, "duration": 30},
    {"name": "James",    "location": "Financial District","avail_start": 645, "avail_end": 720, "duration": 15},
    {"name": "Sandra",   "location": "Marina District",   "avail_start": 375, "avail_end": 480, "duration": 75},
    {"name": "Charles",  "location": "Sunset District",   "avail_start": 120, "avail_end": 420, "duration": 60},
    {"name": "Carol",    "location": "Embarcadero",       "avail_start": 600, "avail_end": 750, "duration": 90},
    {"name": "Helen",    "location": "Presidio",          "avail_start": 210, "avail_end": 330, "duration": 15},
    {"name": "Karen",    "location": "Union Square",      "avail_start": 600, "avail_end": 735, "duration": 60},
    {"name": "John",     "location": "Russian Hill",      "avail_start": 240, "avail_end": 495, "duration": 90},
]

# List of all locations.
locations = [
    "Chinatown", "Fisherman's Wharf", "Mission District", "Richmond District",
    "Financial District", "Marina District", "Sunset District", "Embarcadero",
    "Presidio", "Union Square", "Russian Hill"
]

# Travel distances between locations (in minutes).
# Each key is a tuple (origin, destination).
travel = {
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Russian Hill"): 7,

    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Russian Hill"): 7,

    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Russian Hill"): 15,

    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Russian Hill"): 13,

    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Russian Hill"): 11,

    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Russian Hill"): 8,

    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Russian Hill"): 24,

    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Russian Hill"): 8,

    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Russian Hill"): 14,

    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Russian Hill"): 13,

    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Union Square"): 10,
}

def get_travel_time(origin, destination):
    # Returns the travel time between origin and destination.
    return travel[(origin, destination)]

# -----------------------------
# Z3 Model
# -----------------------------
# Optimize is used to maximize the total number of scheduled meetings.
opt = Optimize()

num_friends = len(friends)

# Decision variables:
# For each friend: a Boolean variable x[i] for whether the meeting is scheduled,
# and an integer start[i] for the meeting’s start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location and arrival time.
starting_location = "Chinatown"
arrival_time = 0

# For each friend scheduled, enforce:
# (a) The meeting cannot start before the friend's available start.
# (b) The meeting (i.e. start time + meeting duration) must finish by the available end.
# (c) The meeting cannot start before you can travel from the starting location to the friend.
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
# For any two scheduled meetings, ensure that one finishes (including its duration and transit time to the next location)
# before the other begins.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        # Either meeting i (plus travel to j) finishes before meeting j starts,
        # OR meeting j (plus travel to i) finishes before meeting i starts.
        no_overlap = Or(start[i] + dur_i + travel_i_j <= start[j],
                        start[j] + dur_j + travel_j_i <= start[i])
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------
# Solve and Print the Schedule
# -----------------------------
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
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")