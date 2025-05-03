from z3 import *

# ---------------------------
# Data definitions
# ---------------------------

# All times are minutes after 9:00AM.
# Friend meeting data: each friend is defined with:
#   name, location, available start time, available end time, and meeting duration.
# Note: Available times are computed as minutes after 9:00AM.
friends = [
    {"name": "Anthony",  "location": "Sunset District",    "avail_start": 585, "avail_end": 780, "duration": 15},  # 6:45PM to 10:00PM
    {"name": "Deborah",  "location": "Richmond District",  "avail_start": 255+180, "avail_end": 300+180, "duration": 30},  # 4:15PM to 5:00PM -> (9:00AM+435, 480)
    {"name": "Rebecca",  "location": "Embarcadero",        "avail_start": 345, "avail_end": 735, "duration": 90},  # 2:45PM to 9:15PM
    {"name": "Joseph",   "location": "The Castro",         "avail_start": 465, "avail_end": 495, "duration": 15},  # 4:45PM to 5:15PM
    {"name": "Linda",    "location": "Bayview",            "avail_start": 525, "avail_end": 780, "duration": 90},  # 5:45PM to 10:00PM
    {"name": "Matthew",  "location": "Golden Gate Park",   "avail_start": 105+180, "avail_end": 585, "duration": 90},  # 1:45PM to 6:45PM (1:45PM=285, so 285; 6:45PM=585)
    {"name": "Lisa",     "location": "Fisherman's Wharf",  "avail_start": 75,  "avail_end": 600, "duration": 15},  # 10:15AM to 7:00PM
    {"name": "Kimberly", "location": "Marina District",    "avail_start": 540, "avail_end": 705, "duration": 75},  # 6:00PM to 8:45PM
    {"name": "Barbara",  "location": "Nob Hill",           "avail_start": 75+180, "avail_end": 150+180, "duration": 60},  # 1:15PM to 2:30PM (1:15PM=255, 2:30PM=330)
    {"name": "Kevin",    "location": "Pacific Heights",    "avail_start": 210, "avail_end": 405, "duration": 90}   # 12:30PM to 3:45PM
]

# Note: Some available times were computed directly. For clarity:
# Anthony: 6:45PM = 585, 10:00PM = 780.
# Deborah: 4:15PM = 435, 5:00PM = 480.
# Rebecca: 2:45PM = 345, 9:15PM = 735.
# Joseph: 4:45PM = 465, 5:15PM = 495.
# Linda: 5:45PM = 525, 10:00PM = 780.
# Matthew: 1:45PM = 285, 6:45PM = 585.
# Lisa: 10:15AM = 75, 7:00PM = 600.
# Kimberly: 6:00PM = 540, 8:45PM = 705.
# Barbara: 1:15PM = 255, 2:30PM = 330.
# Kevin: 12:30PM = 210, 3:45PM = 405.

# List of all locations (and also includes the starting location "Chinatown").
locations = ["Chinatown", "Sunset District", "Richmond District", "Embarcadero",
             "The Castro", "Bayview", "Golden Gate Park", "Fisherman's Wharf",
             "Marina District", "Nob Hill", "Pacific Heights"]

# Travel times between locations (in minutes) as given:
# (origin, destination) : travel time
travel = {
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Pacific Heights"): 10,

    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Pacific Heights"): 21,

    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Pacific Heights"): 10,

    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Pacific Heights"): 11,

    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Pacific Heights"): 16,

    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Pacific Heights"): 23,

    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Pacific Heights"): 16,

    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Pacific Heights"): 12,

    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,

    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,

    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Nob Hill"): 8,
}

def get_travel_time(orig, dest):
    # Returns travel time between two locations; assume the key exists.
    return travel[(orig, dest)]

# -----------------------------
# Z3 Model
# -----------------------------

# We use an Optimize instance so that we can maximize the number of meetings scheduled.
opt = Optimize()

num_friends = len(friends)

# Decision variables:
# x[i] is a Boolean indicating whether meeting with friend i is scheduled.
# start[i] is an integer representing the meeting’s start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -100, start[i] <= 1000)

# Starting location and arrival time.
# You arrive at Chinatown at 9:00AM (time = 0).
start_location = "Chinatown"
arrival_time = 0

# For each meeting, if scheduled then enforce:
# (a) Meeting starts no earlier than friend’s available start time.
# (b) Meeting (start + duration) finishes by the friend’s available end time.
# (c) Meeting start is no earlier than when you can get there from the starting point.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(start_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Non-overlap constraints:
# For any two meetings that are both scheduled, either meeting i (including travel from i's location to j's) finishes before meeting j starts, or vice versa.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        cond = Or(start[i] + dur_i + travel_i_j <= start[j],
                  start[j] + dur_j + travel_j_i <= start[i])
        opt.add(Implies(And(x[i], x[j]), cond))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------
# Solve and Print the Schedule
# -----------------------------
if opt.check() == sat:
    m = opt.model()
    schedule = []
    for i in range(num_friends):
        if m.evaluate(x[i]):
            st = m.evaluate(start[i]).as_long()
            schedule.append((st, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for st, name, loc, dur in schedule:
        finish = st + dur
        def to_time(minutes):
            total = 9 * 60 + minutes
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc}: from {to_time(st)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")