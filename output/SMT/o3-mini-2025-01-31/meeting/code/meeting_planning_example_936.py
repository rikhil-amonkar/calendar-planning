from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are in minutes relative to 9:00AM at Golden Gate Park (time = 0).
# Note how we convert the provided clock times:
# Richard: North Beach, from 12:30PM (210) to 4:00PM (420), duration=105.
# Nancy: Embarcadero, from 11:00AM (120) to 5:30PM (510), duration=30.
# James: Sunset District, from 11:15AM (135) to 9:00PM (720), duration=120.
# Paul: Chinatown, from 7:30PM (630) to 8:15PM (675), duration=15.
# Jeffrey: Russian Hill, from 10:00AM (60) to 7:30PM (630), duration=30.
# Betty: Presidio, from 7:45AM (-75) to 7:00PM (600), duration=45.
# Joseph: Union Square, from 4:30PM (450) to 8:15PM (675), duration=105.
# Laura: Alamo Square, from 12:00PM (180) to 7:00PM (600), duration=90.
# Anthony: Pacific Heights, from 7:15AM (-105) to 8:15AM (-45), duration=45.
# Linda: Haight-Ashbury, from 6:15PM (555) to 7:45PM (645), duration=15.
friends = [
    {"name": "Richard",  "location": "North Beach",       "avail_start": 210, "avail_end": 420, "duration": 105},
    {"name": "Nancy",    "location": "Embarcadero",       "avail_start": 120, "avail_end": 510, "duration": 30},
    {"name": "James",    "location": "Sunset District",   "avail_start": 135, "avail_end": 720, "duration": 120},
    {"name": "Paul",     "location": "Chinatown",         "avail_start": 630, "avail_end": 675, "duration": 15},
    {"name": "Jeffrey",  "location": "Russian Hill",      "avail_start": 60,  "avail_end": 630, "duration": 30},
    {"name": "Betty",    "location": "Presidio",          "avail_start": -75, "avail_end": 600, "duration": 45},
    {"name": "Joseph",   "location": "Union Square",      "avail_start": 450, "avail_end": 675, "duration": 105},
    {"name": "Laura",    "location": "Alamo Square",      "avail_start": 180, "avail_end": 600, "duration": 90},
    {"name": "Anthony",  "location": "Pacific Heights",   "avail_start": -105,"avail_end": -45, "duration": 45},
    {"name": "Linda",    "location": "Haight-Ashbury",    "avail_start": 555, "avail_end": 645, "duration": 15},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Golden Gate Park",
    "North Beach",
    "Embarcadero",
    "Sunset District",
    "Chinatown",
    "Russian Hill",
    "Presidio",
    "Union Square",
    "Alamo Square",
    "Pacific Heights",
    "Haight-Ashbury",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations. (Directional!)
travel = {
    # From Golden Gate Park:
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,

    # From North Beach:
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Haight-Ashbury"): 18,

    # From Embarcadero:
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Haight-Ashbury"): 21,

    # From Sunset District:
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Haight-Ashbury"): 15,

    # From Chinatown:
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,

    # From Russian Hill:
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,

    # From Presidio:
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Haight-Ashbury"): 15,

    # From Union Square:
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Haight-Ashbury"): 18,

    # From Alamo Square:
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,

    # From Pacific Heights:
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,

    # From Haight-Ashbury:
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Pacific Heights"): 12,
}

# Helper to retrieve travel time.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i]: Boolean, whether meeting friend i is scheduled.
# start[i]: Integer, start time of meeting (minutes after 9:00AM at Golden Gate Park).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Golden Gate Park at time 0.
arrival_location = "Golden Gate Park"
arrival_time = 0

# For each friend, if the meeting is scheduled then:
#   - it must start no earlier than the friend’s available start,
#   - and finish (start + duration) by the friend’s available end.
#   - Additionally, you must have time to travel from your starting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Add pairwise non-overlap constraints. For any two scheduled meetings,
# ensure that after finishing one meeting and traveling to the next friend's location,
# the next meeting does not start until after that travel is complete.
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
# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Golden Gate Park):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        # Helper function to convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) to HH:MM.
        def format_time(m):
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")