from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are in minutes after 9:00AM at Chinatown (time = 0).
# Conversion notes:
# Andrew: at Richmond District from 2:00PM to 3:30PM -> [300, 390], min duration = 45.
# Barbara: at The Castro from 6:30PM to 8:30PM -> [570, 690], min duration = 45.
# Helen: at Marina District from 3:15PM to 6:30PM -> [375, 570], min duration = 30.
# Melissa: at Embarcadero from 9:45AM to 1:00PM -> [45, 240], min duration = 120.
# Kevin: at Golden Gate Park from 1:00PM to 4:15PM -> [240, 435], min duration = 90.
# Charles: at Fisherman's Wharf from 2:15PM to 8:15PM -> [315, 675], min duration = 45.
# Ashley: at Russian Hill from 8:15AM to 2:45PM -> [-45, 345], min duration = 120.
# Karen: at Bayview from 7:15PM to 9:45PM -> [615, 765], min duration = 120.
# Richard: at Union Square from 11:00AM to 3:30PM -> [120, 390], min duration = 60.
# Thomas: at Presidio from 3:30PM to 5:45PM -> [390, 525], min duration = 105.
friends = [
    {"name": "Andrew",   "location": "Richmond District",  "avail_start": 300, "avail_end": 390, "duration": 45},
    {"name": "Barbara",  "location": "The Castro",         "avail_start": 570, "avail_end": 690, "duration": 45},
    {"name": "Helen",    "location": "Marina District",    "avail_start": 375, "avail_end": 570, "duration": 30},
    {"name": "Melissa",  "location": "Embarcadero",        "avail_start": 45,  "avail_end": 240, "duration": 120},
    {"name": "Kevin",    "location": "Golden Gate Park",   "avail_start": 240, "avail_end": 435, "duration": 90},
    {"name": "Charles",  "location": "Fisherman's Wharf",  "avail_start": 315, "avail_end": 675, "duration": 45},
    {"name": "Ashley",   "location": "Russian Hill",       "avail_start": -45,"avail_end": 345, "duration": 120},
    {"name": "Karen",    "location": "Bayview",            "avail_start": 615, "avail_end": 765, "duration": 120},
    {"name": "Richard",  "location": "Union Square",       "avail_start": 120, "avail_end": 390, "duration": 60},
    {"name": "Thomas",   "location": "Presidio",           "avail_start": 390, "avail_end": 525, "duration": 105},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Chinatown",
    "Richmond District",
    "The Castro",
    "Marina District",
    "Embarcadero",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Russian Hill",
    "Bayview",
    "Union Square",
    "Presidio",
]

# -----------------------------------------------------------------------------
# Travel distances between locations (in minutes).
travel = {
    # From Chinatown:
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Presidio"): 19,
    
    # From Richmond District:
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Presidio"): 7,
    
    # From The Castro:
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Presidio"): 20,
    
    # From Marina District:
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Presidio"): 10,
    
    # From Embarcadero:
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Presidio"): 20,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Presidio"): 11,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Presidio"): 17,
    
    # From Russian Hill:
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Presidio"): 14,
    
    # From Bayview:
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Presidio"): 32,
    
    # From Union Square:
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    
    # From Presidio:
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22,
}

# Helper function to obtain travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 Model and Optimization.
# -----------------------------------------------------------------------------
# Create an Optimize instance to maximize the number of meetings.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i]: Boolean that determines whether meeting i is scheduled.
#   start[i]: Integer start time (minutes after 9:00AM when at Chinatown) for meeting i.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Chinatown at 9:00AM (time = 0).
arrival_location = "Chinatown"
arrival_time = 0

# For each scheduled meeting, enforce:
#   1. The meeting starts no earlier than the friend's available start time.
#   2. The meeting (start + duration) finishes on or before the available end time.
#   3. You can only begin the meeting after arriving to that location (taking travel time from Chinatown).
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
# For any two scheduled meetings i and j, ensure that,
# after meeting i (plus its travel time from its location to j's location),
# meeting j does not start before that (and vice versa).
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
    
    print("Optimal Schedule (times are minutes after 9:00AM at Chinatown):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        def to_time(m):
            # Convert minutes after 9:00AM (with 9:00AM = 540 minutes after midnight) into HH:MM format.
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(s_time)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")