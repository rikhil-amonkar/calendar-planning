from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# All times are in minutes relative to your arrival at Presidio at 9:00AM (time = 0).
#
# 1. Stephanie at Bayview from 9:00AM to 2:15PM; minimum meeting = 90 minutes.
#    Available window: [0, 315]
# 2. Patricia at Mission District from 12:30PM to 10:00PM; minimum meeting = 45 minutes.
#    12:30PM -> 210 and 10:00PM -> 780.
# 3. Betty at Alamo Square from 7:30PM to 10:00PM; minimum meeting = 90 minutes.
#    7:30PM -> 630 and 10:00PM -> 780.
# 4. Michelle at The Castro from 8:30PM to 10:00PM; minimum meeting = 90 minutes.
#    8:30PM -> 690 and 10:00PM -> 780.
# 5. Linda at North Beach from 10:45AM to 6:00PM; minimum meeting = 90 minutes.
#    10:45AM -> 105 and 6:00PM -> 540.
# 6. Jeffrey at Sunset District from 1:30PM to 9:30PM; minimum meeting = 105 minutes.
#    1:30PM -> 270 and 9:30PM -> 750.
# 7. Anthony at Haight-Ashbury from 11:45AM to 2:30PM; minimum meeting = 30 minutes.
#    11:45AM -> 165 and 2:30PM -> 330.
# 8. James at Embarcadero from 2:30PM to 5:15PM; minimum meeting = 60 minutes.
#    2:30PM -> 330 and 5:15PM -> 495.
# 9. Barbara at Richmond District from 11:15AM to 8:45PM; minimum meeting = 120 minutes.
#    11:15AM -> 135 and 8:45PM -> 765.
# 10. Kevin at Chinatown from 11:30AM to 6:15PM; minimum meeting = 45 minutes.
#     11:30AM -> 150 and 6:15PM -> 555.
friends = [
    {"name": "Stephanie", "location": "Bayview",          "avail_start": 0,   "avail_end": 315, "duration": 90},
    {"name": "Patricia",  "location": "Mission District", "avail_start": 210, "avail_end": 780, "duration": 45},
    {"name": "Betty",     "location": "Alamo Square",     "avail_start": 630, "avail_end": 780, "duration": 90},
    {"name": "Michelle",  "location": "The Castro",       "avail_start": 690, "avail_end": 780, "duration": 90},
    {"name": "Linda",     "location": "North Beach",      "avail_start": 105, "avail_end": 540, "duration": 90},
    {"name": "Jeffrey",   "location": "Sunset District",  "avail_start": 270, "avail_end": 750, "duration": 105},
    {"name": "Anthony",   "location": "Haight-Ashbury",   "avail_start": 165, "avail_end": 330, "duration": 30},
    {"name": "James",     "location": "Embarcadero",      "avail_start": 330, "avail_end": 495, "duration": 60},
    {"name": "Barbara",   "location": "Richmond District","avail_start": 135, "avail_end": 765, "duration": 120},
    {"name": "Kevin",     "location": "Chinatown",        "avail_start": 150, "avail_end": 555, "duration": 45},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Presidio",
    "Bayview",
    "Mission District",
    "Alamo Square",
    "The Castro",
    "North Beach",
    "Sunset District",
    "Haight-Ashbury",
    "Embarcadero",
    "Richmond District",
    "Chinatown",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes)
# The keys are (origin, destination) tuples.
travel = {
    # From Presidio:
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Chinatown"): 21,

    # From Bayview:
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Chinatown"): 19,

    # From Mission District:
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Chinatown"): 16,

    # From Alamo Square:
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Chinatown"): 15,

    # From The Castro:
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Chinatown"): 22,

    # From North Beach:
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Chinatown"): 6,

    # From Sunset District:
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Chinatown"): 30,

    # From Haight-Ashbury:
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Chinatown"): 19,

    # From Embarcadero:
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Chinatown"): 7,

    # From Richmond District:
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Chinatown"): 20,

    # From Chinatown:
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Richmond District"): 20,
}

# Helper function to get travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use the Optimize() from Z3 to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i:
#   x[i] is a Boolean decision variable that is True if you meet friend i.
#   start[i] is an integer variable representing the meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Presidio at time 0.
starting_location = "Presidio"
arrival_time = 0

# For each friend, if the meeting is scheduled then:
#   - Its start time is at or after the friend’s available start.
#   - Its end time (start + duration) is before the available end.
#   - There is enough time to travel from the starting point (Presidio) to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(starting_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Add pairwise non-overlap constraints.
# For any two scheduled meetings i and j, enforce that either:
#   Meeting i (plus its duration and travel to j) finishes before j starts,
# or meeting j (plus its duration and travel to i) finishes before i starts.
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

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve the optimization and print the schedule.
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
            # Convert minutes relative to 9:00AM to HH:MM format.
            total = 540 + minutes  # because 9:00AM is 540 minutes after midnight
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")