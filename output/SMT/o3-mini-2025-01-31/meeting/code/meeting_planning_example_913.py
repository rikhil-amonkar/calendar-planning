from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# All times are in minutes relative to 9:00AM.
#
# 1. Mark      at The Castro       from 11:15AM to 12:45PM; meeting >= 45 minutes.
#    11:15AM = 135, 12:45PM = 165.
# 2. Sandra    at Haight-Ashbury   from 10:45AM to 12:45PM; meeting >= 105 minutes.
#    10:45AM = 105, 12:45PM = 165.
# 3. Daniel    at North Beach      from 10:30AM to 7:15PM; meeting >= 30 minutes.
#    10:30AM = 90, 7:15PM = 615.
# 4. Brian     at Mission District from 4:45PM to 7:30PM; meeting >= 15 minutes.
#    4:45PM = 465, 7:30PM = 630.
# 5. Kenneth   at Pacific Heights  from 4:00PM to 9:00PM; meeting >= 60 minutes.
#    4:00PM = 420, 9:00PM = 720.
# 6. George    at Chinatown        from 10:00AM to 1:15PM; meeting >= 105 minutes.
#    10:00AM = 60, 1:15PM = 255.
# 7. Lisa      at Bayview          from 8:30PM to 10:00PM; meeting >= 90 minutes.
#    8:30PM = 690, 10:00PM = 780.
# 8. Jeffrey   at Fisherman's Wharf from 6:15PM to 8:45PM; meeting >= 90 minutes.
#    6:15PM = 555, 8:45PM = 705.
# 9. Charles   at Financial District from 11:15AM to 1:45PM; meeting >= 30 minutes.
#    11:15AM = 135, 1:45PM = 285.
# 10. Richard  at Union Square     from 4:00PM to 5:00PM; meeting >= 45 minutes.
#    4:00PM = 420, 5:00PM = 480.
friends = [
    {"name": "Mark",    "location": "The Castro",       "avail_start": 135, "avail_end": 165, "duration": 45},
    {"name": "Sandra",  "location": "Haight-Ashbury",   "avail_start": 105, "avail_end": 165, "duration": 105},
    {"name": "Daniel",  "location": "North Beach",      "avail_start": 90,  "avail_end": 615, "duration": 30},
    {"name": "Brian",   "location": "Mission District", "avail_start": 465, "avail_end": 630, "duration": 15},
    {"name": "Kenneth", "location": "Pacific Heights",  "avail_start": 420, "avail_end": 720, "duration": 60},
    {"name": "George",  "location": "Chinatown",        "avail_start": 60,  "avail_end": 255, "duration": 105},
    {"name": "Lisa",    "location": "Bayview",          "avail_start": 690, "avail_end": 780, "duration": 90},
    {"name": "Jeffrey", "location": "Fisherman's Wharf","avail_start": 555, "avail_end": 705, "duration": 90},
    {"name": "Charles", "location": "Financial District", "avail_start": 135, "avail_end": 285, "duration": 30},
    {"name": "Richard", "location": "Union Square",     "avail_start": 420, "avail_end": 480, "duration": 45},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Sunset District",
    "The Castro",
    "Haight-Ashbury",
    "North Beach",
    "Mission District",
    "Pacific Heights",
    "Chinatown",
    "Bayview",
    "Fisherman's Wharf",
    "Financial District",
    "Union Square",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# The keys are tuples (origin, destination). Data provided below.
travel = {
    # From Sunset District:
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Union Square"): 30,

    # From The Castro:
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Union Square"): 19,

    # From Haight-Ashbury:
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,

    # From North Beach:
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Union Square"): 7,

    # From Mission District:
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,

    # From Pacific Heights:
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,

    # From Chinatown:
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Union Square"): 7,

    # From Bayview:
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Union Square"): 18,

    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,

    # From Financial District:
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Union Square"): 9,

    # From Union Square:
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Financial District"): 9,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use the Optimize module to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i:
#    x[i] is True if a meeting is scheduled.
#    start[i] is the meeting’s start time (in minutes relative to 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location: Sunset District at 9:00AM (time 0).
starting_location = "Sunset District"
arrival_time = 0

# For each scheduled friend, enforce:
#  - Meeting start must be no earlier than the friend’s available start.
#  - Meeting plus its duration must finish by the friend’s available end.
#  - There is enough time to get from the starting location.
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
# For every pair of meetings (if both are scheduled), ensure that one meeting (plus travel time)
# finishes before the other begins.
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