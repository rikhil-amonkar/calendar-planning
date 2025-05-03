from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# Times are measured in minutes relative to 9:00AM at North Beach (time = 0).
# Note: If the friend’s available start time is before 9:00AM, we set it accordingly (it will be overridden by travel constraints).
#
# George: The Castro, available 4:30PM-7:30PM -> [450, 630], meeting >= 60 mins.
# Anthony: Haight-Ashbury, available 7:45PM-9:45PM -> [645, 765], meeting >= 60 mins.
# Kimberly: Richmond District, available 3:15PM-5:45PM -> [375, 525], meeting >= 120 mins.
# Ronald: Mission District, available 5:45PM-9:00PM -> [525, 720], meeting >= 105 mins.
# Kenneth: Union Square, available 12:45PM-5:45PM -> [225, 525], meeting >= 105 mins.
# Patricia: Sunset District, available 9:00PM-9:45PM -> [720, 765], meeting >= 45 mins.
# Matthew: Financial District, available 9:45PM-10:30PM -> [765, 810], meeting >= 45 mins.
# Amanda: Presidio, available 9:30PM-10:30PM -> [750, 810], meeting >= 45 mins.
# Steven: Golden Gate Park, available 12:15PM-6:15PM -> [195, 555], meeting >= 105 mins.
# Elizabeth: Embarcadero, available 8:00AM-10:30AM -> [ -60, 90 ], meeting >= 90 mins.
friends = [
    {"name": "George",    "location": "The Castro",       "avail_start": 450, "avail_end": 630, "duration": 60},
    {"name": "Anthony",   "location": "Haight-Ashbury",    "avail_start": 645, "avail_end": 765, "duration": 60},
    {"name": "Kimberly",  "location": "Richmond District", "avail_start": 375, "avail_end": 525, "duration": 120},
    {"name": "Ronald",    "location": "Mission District",  "avail_start": 525, "avail_end": 720, "duration": 105},
    {"name": "Kenneth",   "location": "Union Square",      "avail_start": 225, "avail_end": 525, "duration": 105},
    {"name": "Patricia",  "location": "Sunset District",   "avail_start": 720, "avail_end": 765, "duration": 45},
    {"name": "Matthew",   "location": "Financial District","avail_start": 765, "avail_end": 810, "duration": 45},
    {"name": "Amanda",    "location": "Presidio",          "avail_start": 750, "avail_end": 810, "duration": 45},
    {"name": "Steven",    "location": "Golden Gate Park",  "avail_start": 195, "avail_end": 555, "duration": 105},
    {"name": "Elizabeth", "location": "Embarcadero",       "avail_start": -60, "avail_end": 90,  "duration": 90},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "North Beach",
    "The Castro",
    "Haight-Ashbury",
    "Richmond District",
    "Mission District",
    "Union Square",
    "Sunset District",
    "Financial District",
    "Presidio",
    "Golden Gate Park",
    "Embarcadero",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
travel = {
    # From North Beach:
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    
    # From The Castro:
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Embarcadero"): 22,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    
    # From Richmond District:
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    
    # From Mission District:
    ("Mission District", "North Beach"): 17,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 25,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Embarcadero"): 19,
    
    # From Union Square:
    ("Union Square", "North Beach"): 10,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    
    # From Sunset District:
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Embarcadero"): 30,
    
    # From Financial District:
    ("Financial District", "North Beach"): 7,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Embarcadero"): 4,
    
    # From Presidio:
    ("Presidio", "North Beach"): 18,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Embarcadero"): 20,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Embarcadero"): 25,
    
    # From Embarcadero:
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
}

# Helper function to obtain the travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize() from Z3 to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i] is a Boolean indicating whether to schedule friend i.
# start[i] is an integer for the meeting start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set wide bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at North Beach at 9:00AM (time = 0).
arrival_location = "North Beach"
arrival_time = 0

# For each friend meeting scheduled, enforce:
# 1. Meeting does not start before friend’s available start.
# 2. Meeting (plus its duration) is finished by the friend’s available end.
# 3. Meeting cannot start before you have travelled from North Beach.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Add pairwise non-overlap constraints.
# For any two scheduled meetings, ensure one finishes (plus travel time to the next meeting’s location)
# before the other starts.
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

# Objective: maximize total number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the scheduled itinerary.
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at North Beach):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        def to_time(m):
            # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) to HH:MM.
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(s_time)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")