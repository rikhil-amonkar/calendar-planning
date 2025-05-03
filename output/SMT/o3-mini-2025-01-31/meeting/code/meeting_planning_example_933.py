from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# All times are measured in minutes after 9:00AM (arrival at Nob Hill, time = 0).
# Time conversions:
#   Helen: Sunset District, 11:45AM - 1:15PM -> avail [165, 255], duration 60.
#   Joseph: Pacific Heights, 11:45AM - 8:45PM -> avail [165, 705], duration 60.
#   Laura: The Castro, 12:00PM - 4:30PM -> avail [180, 450], duration 90.
#   Deborah: Union Square, 1:30PM - 5:30PM -> avail [270, 510], duration 15.
#   William: Golden Gate Park, 5:30PM - 10:00PM -> avail [510, 780], duration 75.
#   Jason: Bayview, 12:00PM - 5:45PM -> avail [180, 525], duration 75.
#   Mark: Haight-Ashbury, 9:15AM - 10:00AM -> avail [15, 60], duration 30.
#   Margaret: Richmond District, 7:45AM - 5:15PM -> avail [-75, 495], duration 75.
#   Steven: Financial District, 12:00PM - 8:15PM -> avail [180, 675], duration 90.
#   Kenneth: North Beach, 7:30PM - 9:30PM -> avail [630, 750], duration 90.
friends = [
    {"name": "Helen",     "location": "Sunset District",      "avail_start": 165,  "avail_end": 255,  "duration": 60},
    {"name": "Joseph",    "location": "Pacific Heights",      "avail_start": 165,  "avail_end": 705,  "duration": 60},
    {"name": "Laura",     "location": "The Castro",           "avail_start": 180,  "avail_end": 450,  "duration": 90},
    {"name": "Deborah",   "location": "Union Square",         "avail_start": 270,  "avail_end": 510,  "duration": 15},
    {"name": "William",   "location": "Golden Gate Park",     "avail_start": 510,  "avail_end": 780,  "duration": 75},
    {"name": "Jason",     "location": "Bayview",              "avail_start": 180,  "avail_end": 525,  "duration": 75},
    {"name": "Mark",      "location": "Haight-Ashbury",       "avail_start": 15,   "avail_end": 60,   "duration": 30},
    {"name": "Margaret",  "location": "Richmond District",    "avail_start": -75,  "avail_end": 495,  "duration": 75},
    {"name": "Steven",    "location": "Financial District",   "avail_start": 180,  "avail_end": 675,  "duration": 90},
    {"name": "Kenneth",   "location": "North Beach",          "avail_start": 630,  "avail_end": 750,  "duration": 90},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Nob Hill",
    "Sunset District",
    "Pacific Heights",
    "The Castro",
    "Union Square",
    "Golden Gate Park",
    "Bayview",
    "Haight-Ashbury",
    "Richmond District",
    "Financial District",
    "North Beach",
]

# -----------------------------------------------------------------------------
# Travel distances between locations (in minutes)
travel = {
    # From Nob Hill:
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "North Beach"): 8,
    
    # From Sunset District:
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "North Beach"): 28,
    
    # From Pacific Heights:
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "North Beach"): 9,
    
    # From The Castro:
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "North Beach"): 20,
    
    # From Union Square:
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "North Beach"): 10,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    
    # From Bayview:
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "North Beach"): 22,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "North Beach"): 19,
    
    # From Richmond District:
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    
    # From Financial District:
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    
    # From North Beach:
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
}

# Helper function to get travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 Model, constraints and optimization.
# -----------------------------------------------------------------------------
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i] is a Boolean indicating whether friend i's meeting is scheduled.
# start[i] is the meeting start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Arrival is at Nob Hill at 9:00AM (time = 0).
arrival_location = "Nob Hill"
arrival_time = 0

# For each scheduled meeting i, enforce:
# 1. The meeting begins no earlier than the friend’s available start time.
# 2. The meeting (start + duration) ends no later than the friend’s available end.
# 3. You can only start the meeting after arriving from Nob Hill (including travel time from Nob Hill to that location).
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
# If two meetings are both scheduled, then one must finish (plus travel time to the other)
# before the other meeting begins.
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
# Solve and output the schedule.
# -----------------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Nob Hill):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        def format_time(m):
            # Convert minutes after 9:00AM (9:00 = 540 minutes after midnight) to HH:MM string.
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")