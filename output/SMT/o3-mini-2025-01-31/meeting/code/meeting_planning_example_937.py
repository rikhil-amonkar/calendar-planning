from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# All times are in minutes relative to 9:00AM at Russian Hill (time=0).
# The available windows converted:
# David: Sunset District from 9:15AM to 10:00PM  --> [15, 780], duration >= 15.
# Kenneth: Union Square from 9:15PM to 9:45PM        --> [735, 765], duration >= 15.
# Patricia: Nob Hill from 3:00PM to 7:15PM            --> [360, 615], duration >= 120.
# Mary: Marina District from 2:45PM to 4:45PM         --> [345, 465], duration >= 45.
# Charles: Richmond District from 5:15PM to 9:00PM      --> [495, 720], duration >= 15.
# Joshua: Financial District from 2:30PM to 5:15PM      --> [330, 495], duration >= 90.
# Ronald: Embarcadero from 6:15PM to 8:45PM             --> [555, 705], duration >= 30.
# George: The Castro from 2:15PM to 7:00PM              --> [315, 600], duration >= 105.
# Kimberly: Alamo Square from 9:00AM to 2:30PM          --> [0, 330], duration >= 105.
# William: Presidio from 7:00AM to 12:45PM              --> [ -120, 225], duration >= 60.
friends = [
    {"name": "David",     "location": "Sunset District",    "avail_start": 15,   "avail_end": 780, "duration": 15},
    {"name": "Kenneth",   "location": "Union Square",       "avail_start": 735,  "avail_end": 765, "duration": 15},
    {"name": "Patricia",  "location": "Nob Hill",           "avail_start": 360,  "avail_end": 615, "duration": 120},
    {"name": "Mary",      "location": "Marina District",    "avail_start": 345,  "avail_end": 465, "duration": 45},
    {"name": "Charles",   "location": "Richmond District",  "avail_start": 495,  "avail_end": 720, "duration": 15},
    {"name": "Joshua",    "location": "Financial District", "avail_start": 330,  "avail_end": 495, "duration": 90},
    {"name": "Ronald",    "location": "Embarcadero",        "avail_start": 555,  "avail_end": 705, "duration": 30},
    {"name": "George",    "location": "The Castro",         "avail_start": 315,  "avail_end": 600, "duration": 105},
    {"name": "Kimberly",  "location": "Alamo Square",       "avail_start": 0,    "avail_end": 330, "duration": 105},
    {"name": "William",   "location": "Presidio",           "avail_start": -120, "avail_end": 225, "duration": 60},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Russian Hill",       # Arrival (starting point)
    "Sunset District",
    "Union Square",
    "Nob Hill",
    "Marina District",
    "Richmond District",
    "Financial District",
    "Embarcadero",
    "The Castro",
    "Alamo Square",
    "Presidio",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# They are directional as given.
travel = {
    # From Russian Hill:
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,

    # From Sunset District:
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Presidio"): 16,

    # From Union Square:
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,

    # From Nob Hill:
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,

    # From Marina District:
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,

    # From Richmond District:
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Presidio"): 7,

    # From Financial District:
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,

    # From Embarcadero:
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Presidio"): 20,

    # From The Castro:
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Presidio"): 20,

    # From Alamo Square:
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Presidio"): 17,

    # From Presidio:
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Alamo Square"): 19,
}

# Helper: get travel time from origin to destination.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i] is a Boolean indicating whether we schedule a meeting with friend i.
#   start[i] is an integer giving the meeting start time (in minutes from 9:00AM at Russian Hill).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow a wide range of possible start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Russian Hill at time = 0.
arrival_location = "Russian Hill"
arrival_time = 0

# For each friend, if the meeting is scheduled then:
# - The meeting must start no earlier than the friend's available start,
# - Must finish (start + duration) before the friend's available end,
# - And you must have enough time to travel from your starting point (Russian Hill) to the friend's location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Add pairwise non-overlap constraints.
# For any two scheduled meetings, enforce that the first meeting (plus its duration and travel time to the next location)
# finishes before the second meeting starts OR vice versa.
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

# Objective: maximize the number of meetings scheduled.
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
    schedule.sort(key=lambda item: item[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Russian Hill):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        # Helper function to convert minutes relative to 9:00AM into a HH:MM string.
        def format_time(m):
            total = 540 + m  # 9:00AM = 540 minutes after midnight.
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")