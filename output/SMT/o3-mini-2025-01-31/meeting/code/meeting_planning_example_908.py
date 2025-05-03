from z3 import *

# ---------------------------------------------------------------------
# Friend definitions
#
# Times are measured in minutes after 9:00AM.
# Convert each friend’s availability window relative to 9:00AM:
#
# 1. Mark at Fisherman's Wharf: 8:15AM to 10:00AM becomes [-45, 60].
#    Minimum meeting duration: 30 minutes.
# 2. Stephanie at Presidio: 12:15PM to 3:00PM becomes [195, 360].
#    Minimum meeting duration: 75 minutes.
# 3. Betty at Bayview: 7:15AM to 8:30PM becomes [-105, 690].
#    Minimum meeting duration: 15 minutes.
# 4. Lisa at Haight-Ashbury: 3:30PM to 6:30PM becomes [390, 570].
#    Minimum meeting duration: 45 minutes.
# 5. William at Russian Hill: 6:45PM to 8:00PM becomes [585, 660].
#    Minimum meeting duration: 60 minutes.
# 6. Brian at The Castro: 9:15AM to 1:15PM becomes [15, 255].
#    Minimum meeting duration: 30 minutes.
# 7. Joseph at Marina District: 10:45AM to 3:00PM becomes [105, 360].
#    Minimum meeting duration: 90 minutes.
# 8. Ashley at Richmond District: 9:45AM to 11:15AM becomes [45, 75].
#    Minimum meeting duration: 45 minutes.
# 9. Patricia at Union Square: 4:30PM to 8:00PM becomes [450, 660].
#    Minimum meeting duration: 120 minutes.
# 10. Karen at Sunset District: 4:30PM to 10:00PM becomes [450, 780].
#     Minimum meeting duration: 105 minutes.
#
friends = [
    {"name": "Mark",      "location": "Fisherman's Wharf",  "avail_start": -45, "avail_end": 60,  "duration": 30},
    {"name": "Stephanie", "location": "Presidio",           "avail_start": 195, "avail_end": 360, "duration": 75},
    {"name": "Betty",     "location": "Bayview",            "avail_start": -105, "avail_end": 690, "duration": 15},
    {"name": "Lisa",      "location": "Haight-Ashbury",     "avail_start": 390, "avail_end": 570, "duration": 45},
    {"name": "William",   "location": "Russian Hill",       "avail_start": 585, "avail_end": 660, "duration": 60},
    {"name": "Brian",     "location": "The Castro",         "avail_start": 15,  "avail_end": 255, "duration": 30},
    {"name": "Joseph",    "location": "Marina District",    "avail_start": 105, "avail_end": 360, "duration": 90},
    {"name": "Ashley",    "location": "Richmond District",  "avail_start": 45,  "avail_end": 75,  "duration": 45},
    {"name": "Patricia",  "location": "Union Square",       "avail_start": 450, "avail_end": 660, "duration": 120},
    {"name": "Karen",     "location": "Sunset District",    "avail_start": 450, "avail_end": 780, "duration": 105},
]

# ---------------------------------------------------------------------
# List of locations – these include all friend meeting places plus the starting point.
locations = [
    "Financial District",
    "Fisherman's Wharf",
    "Presidio",
    "Bayview",
    "Haight-Ashbury",
    "Russian Hill",
    "The Castro",
    "Marina District",
    "Richmond District",
    "Union Square",
    "Sunset District"
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes)
# Each key is a tuple (origin, destination)
travel = {
    # Financial District distances:
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,

    # Fisherman's Wharf distances:
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,

    # Presidio distances:
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,

    # Bayview distances:
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,

    # Haight-Ashbury distances:
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,

    # Russian Hill distances:
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,

    # The Castro distances:
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,

    # Marina District distances:
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,

    # Richmond District distances:
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,

    # Union Square distances:
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,

    # Sunset District distances:
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Union Square"): 30,
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
# x[i] is True if meeting with friend i is scheduled.
# start[i] is the start time (minutes after 9:00AM) for friend i's meeting.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location is Financial District at time 0.
starting_location = "Financial District"
arrival_time = 0

# For each scheduled meeting, enforce that:
#   (a) meeting starts no earlier than friend's available start.
#   (b) meeting finishes (start + duration) by friend's available end.
#   (c) meeting cannot start before you've reached the friend from the starting point.
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
# For any two scheduled meetings, ensure that one meeting (plus travel)
# finishes before the other starts.
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

# Objective: maximize total meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the schedule
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