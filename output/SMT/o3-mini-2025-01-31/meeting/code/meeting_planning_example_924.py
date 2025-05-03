from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# Times are expressed in minutes relative to your arrival at Presidio at 9:00AM (time = 0).
# Conversion example: 11:15AM -> 135 (i.e. 2h15 after 9:00AM), 8:15PM -> 675 (11h15 after 9:00AM)

friends = [
    {"name": "Charles",  "location": "The Castro",         "avail_start": 135, "avail_end": 675, "duration": 15},
    {"name": "Rebecca",  "location": "Alamo Square",       "avail_start": 375, "avail_end": 750, "duration": 30},
    {"name": "Deborah",  "location": "Financial District", "avail_start": 630, "avail_end": 780, "duration": 120},
    {"name": "Linda",    "location": "Marina District",    "avail_start": 0,   "avail_end": 405, "duration": 60},
    {"name": "Jason",    "location": "Haight-Ashbury",     "avail_start": 420, "avail_end": 600, "duration": 120},
    {"name": "Richard",  "location": "Embarcadero",        "avail_start": 210, "avail_end": 660, "duration": 45},
    {"name": "Paul",     "location": "Nob Hill",           "avail_start": 480, "avail_end": 645, "duration": 60},
    {"name": "Kenneth",  "location": "Union Square",       "avail_start": 615, "avail_end": 765, "duration": 105},
    {"name": "William",  "location": "Mission District",   "avail_start": 90,  "avail_end": 555, "duration": 60},
    {"name": "Karen",    "location": "Golden Gate Park",   "avail_start": 375, "avail_end": 765, "duration": 45},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Presidio",
    "The Castro",
    "Alamo Square",
    "Financial District",
    "Marina District",
    "Haight-Ashbury",
    "Embarcadero",
    "Nob Hill",
    "Union Square",
    "Mission District",
    "Golden Gate Park",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes), as provided.
travel = {
    # From Presidio:
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Golden Gate Park"): 12,
    
    # From The Castro:
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Golden Gate Park"): 11,
    
    # From Alamo Square:
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    
    # From Financial District:
    ("Financial District", "Presidio"): 22,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Golden Gate Park"): 23,
    
    # From Marina District:
    ("Marina District", "Presidio"): 10,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Golden Gate Park"): 18,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    
    # From Embarcadero:
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    
    # From Nob Hill:
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
    
    # From Union Square:
    ("Union Square", "Presidio"): 24,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    
    # From Mission District:
    ("Mission District", "Presidio"): 25,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
}

# Helper function to retrieve travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize() to try to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#  x[i] is a Boolean variable which is True if we schedule a meeting with friend i.
#  start[i] is an integer variable representing the meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Give wide bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Presidio at 9:00AM, so arrival_time = 0.
arrival_location = "Presidio"
arrival_time = 0

# For each meeting that is scheduled, enforce:
# 1. The meeting does not start before the friend's available start.
# 2. The meeting (plus its duration) must finish by the friend's available end.
# 3. Sufficient travel time is available from the arrival location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Pairwise non-overlap constraints:
# For any two meetings that are both scheduled, enforce that one finishes (plus travel time to the next meeting’s location)
# before the other begins.
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
        if is_true(model.evaluate(x[i])):
            t_val = model.evaluate(start[i]).as_long()
            schedule.append((t_val, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM at Presidio):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) to HH:MM.
            total = 540 + minutes
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")