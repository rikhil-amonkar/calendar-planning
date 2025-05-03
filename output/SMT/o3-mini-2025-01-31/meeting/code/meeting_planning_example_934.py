from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# All times are minutes after 9:00AM (arrival at Nob Hill, time=0).
# Note: We convert the specified times to minutes relative to 9:00AM.
#   Mary: Embarcadero, 8:00PM to 9:15PM -> [660, 735], min duration 75.
#   Kenneth: The Castro, 11:15AM to 7:15PM -> [75+?] Let's compute:
#            11:15AM: 2h15 after 9:00 = 135; 7:15PM: 10h15 = 615, min duration 30.
#   Joseph: Haight-Ashbury, 8:00PM to 10:00PM -> [660, 780], min duration 120.
#   Sarah: Union Square, 11:45AM to 2:30PM -> [165, 330], min duration 90.
#   Thomas: North Beach, 7:15PM to 7:45PM -> [615, 645], min duration 15.
#   Daniel: Pacific Heights, 1:45PM to 8:30PM -> [285, 690], min duration 15.
#   Richard: Chinatown, 8:00AM to 6:45PM -> [-60, 585], min duration 30.
#   Mark: Golden Gate Park, 5:30PM to 9:30PM -> [510, 750], min duration 120.
#   David: Marina District, 8:00PM to 9:00PM -> [660, 720], min duration 60.
#   Karen: Russian Hill, 1:15PM to 6:30PM -> [255, 570], min duration 120.
friends = [
    {"name": "Mary",     "location": "Embarcadero",    "avail_start": 660, "avail_end": 735, "duration": 75},
    {"name": "Kenneth",  "location": "The Castro",     "avail_start": 135, "avail_end": 615, "duration": 30},
    {"name": "Joseph",   "location": "Haight-Ashbury", "avail_start": 660, "avail_end": 780, "duration": 120},
    {"name": "Sarah",    "location": "Union Square",   "avail_start": 165, "avail_end": 330, "duration": 90},
    {"name": "Thomas",   "location": "North Beach",    "avail_start": 615, "avail_end": 645, "duration": 15},
    {"name": "Daniel",   "location": "Pacific Heights","avail_start": 285, "avail_end": 690, "duration": 15},
    {"name": "Richard",  "location": "Chinatown",      "avail_start": -60, "avail_end": 585, "duration": 30},
    {"name": "Mark",     "location": "Golden Gate Park","avail_start": 510, "avail_end": 750, "duration": 120},
    {"name": "David",    "location": "Marina District","avail_start": 660, "avail_end": 720, "duration": 60},
    {"name": "Karen",    "location": "Russian Hill",   "avail_start": 255, "avail_end": 570, "duration": 120},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Nob Hill",
    "Embarcadero",
    "The Castro",
    "Haight-Ashbury",
    "Union Square",
    "North Beach",
    "Pacific Heights",
    "Chinatown",
    "Golden Gate Park",
    "Marina District",
    "Russian Hill",
]

# -----------------------------------------------------------------------------
# Travel distances between locations (in minutes).
travel = {
    # From Nob Hill:
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Russian Hill"): 5,
    
    # From Embarcadero:
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Russian Hill"): 8,
    
    # From The Castro:
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Russian Hill"): 18,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Russian Hill"): 17,
    
    # From Union Square:
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Russian Hill"): 13,
    
    # From North Beach:
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Chinatown"): 3,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Russian Hill"): 4,
    
    # From Pacific Heights:
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Russian Hill"): 7,
    
    # From Chinatown:
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Russian Hill"): 7,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    
    # From Marina District:
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    
    # From Russian Hill:
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7,
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
#   x[i]: Boolean; whether meeting i is scheduled.
#   start[i]: meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow start times in a wide bound (say -300 to 1000 minutes).
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Arrival at Nob Hill is at time 0.
arrival_location = "Nob Hill"
arrival_time = 0

# For each meeting, if scheduled, enforce:
#  - The start time is no earlier than the friend’s available start time.
#  - The meeting (start+duration) finishes before or at the friend’s available end.
#  - You can only start after arriving from Nob Hill (i.e. arrival_time + travel from Nob Hill to location).
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
# If two meetings i and j are both scheduled, then either:
#   meeting i (plus its duration and travel from its location to j's location)
#   finishes before meeting j starts, or vice versa.
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
        # Convert minutes after 9:00AM to HH:MM format (9:00AM = 540 minutes after midnight)
        def format_time(m):
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")