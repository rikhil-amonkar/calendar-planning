from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# All times are in minutes after 9:00AM at Haight-Ashbury (time = 0).
# We convert the given times accordingly:
#   Amanda: at Union Square from 11:00AM to 2:30PM => [120, 330], duration=90.
#   George: at Embarcadero from 4:15PM to 8:30PM => [435, 690], duration=120.
#   Thomas: at Golden Gate Park from 8:15AM to 4:45PM => [ -45, 465 ], duration=30.
#   Helen: at Alamo Square from 12:30PM to 1:30PM => [210, 270], duration=45.
#   Stephanie: at Chinatown from 8:15AM to 10:00PM => [ -45, 780 ], duration=60.
#   Timothy: at The Castro from 7:15PM to 9:30PM => [615, 750], duration=60.
#   Jason: at North Beach from 4:15PM to 6:30PM => [435, 570], duration=75.
#   Mark: at Pacific Heights from 12:45PM to 5:00PM => [195, 480], duration=15.
#   Barbara: at Mission District from 5:00PM to 9:15PM => [480, 750], duration=45.
#   Karen: at Financial District from 1:30PM to 6:30PM => [270, 570], duration=120.
friends = [
    {"name": "Amanda",    "location": "Union Square",      "avail_start": 120, "avail_end": 330, "duration": 90},
    {"name": "George",    "location": "Embarcadero",       "avail_start": 435, "avail_end": 690, "duration": 120},
    {"name": "Thomas",    "location": "Golden Gate Park",  "avail_start": -45, "avail_end": 465, "duration": 30},
    {"name": "Helen",     "location": "Alamo Square",      "avail_start": 210, "avail_end": 270, "duration": 45},
    {"name": "Stephanie", "location": "Chinatown",         "avail_start": -45, "avail_end": 780, "duration": 60},
    {"name": "Timothy",   "location": "The Castro",        "avail_start": 615, "avail_end": 750, "duration": 60},
    {"name": "Jason",     "location": "North Beach",       "avail_start": 435, "avail_end": 570, "duration": 75},
    {"name": "Mark",      "location": "Pacific Heights",   "avail_start": 195, "avail_end": 480, "duration": 15},
    {"name": "Barbara",   "location": "Mission District",  "avail_start": 480, "avail_end": 750, "duration": 45},
    {"name": "Karen",     "location": "Financial District","avail_start": 270, "avail_end": 570, "duration": 120},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Haight-Ashbury",
    "Union Square",
    "Embarcadero",
    "Golden Gate Park",
    "Alamo Square",
    "Chinatown",
    "The Castro",
    "North Beach",
    "Pacific Heights",
    "Mission District",
    "Financial District",
]

# -----------------------------------------------------------------------------
# Travel distances between locations (in minutes)
# Note: the travel times are directional.
travel = {
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Financial District"): 21,
    
    # From Union Square:
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Financial District"): 9,
    
    # From Embarcadero:
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Financial District"): 5,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Financial District"): 26,
    
    # From Alamo Square:
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Financial District"): 17,
    
    # From Chinatown:
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Financial District"): 5,
    
    # From The Castro:
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 21,
    
    # From North Beach:
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Financial District"): 8,
    
    # From Pacific Heights:
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Financial District"): 13,
    
    # From Mission District:
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Financial District"): 15,
    
    # From Financial District:
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
}

# Helper function to get travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i]: a Boolean that indicates whether you schedule friend i.
# start[i]: meeting start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Add wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Arrival is at Haight-Ashbury, at time 0.
arrival_location = "Haight-Ashbury"
arrival_time = 0

# For each scheduled meeting, enforce that:
# 1. The meeting starts no earlier than the friend’s available start.
# 2. The meeting (start + duration) ends no later than the friend’s available end.
# 3. You can only get there after departing from Haight-Ashbury (arrival_time + travel).
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
# If meetings i and j are both scheduled, then either i (plus its duration plus travel from i to j)
# finishes before j starts, or vice versa.
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
        # Utility to convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) to HH:MM
        def format_time(m):
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")