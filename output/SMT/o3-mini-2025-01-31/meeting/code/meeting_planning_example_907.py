from z3 import *

# ---------------------------------------------------------------------
# Friend definitions:
#
# Times are in minutes after 9:00AM.
#
# Friend data:
# 1. Jeffrey: Golden Gate Park, avail 3:00PM–6:00PM, i.e. [360, 540], duration ≥ 30 minutes.
# 2. Melissa: Sunset District, avail 7:00PM–10:00PM, i.e. [600, 780], duration ≥ 120 minutes.
# 3. Andrew: Alamo Square, avail 10:15AM–2:45PM, i.e. [75, 345], duration ≥ 15 minutes.
# 4. Robert: Embarcadero, avail 7:00PM–9:15PM, i.e. [600, 750], duration ≥ 15 minutes.
# 5. Laura: Union Square, avail 3:00PM–5:30PM, i.e. [360, 510], duration ≥ 120 minutes.
# 6. Patricia: Chinatown, avail 12:15PM–6:30PM, i.e. [195, 570], duration ≥ 120 minutes.
# 7. Margaret: Richmond District, avail 3:45PM–9:45PM, i.e. [405, 765], duration ≥ 120 minutes.
# 8. George: Marina District, avail 6:30PM–9:30PM, i.e. [570, 750], duration ≥ 60 minutes.
# 9. Jason: Bayview, avail 8:45PM–9:45PM, i.e. [705, 765], duration ≥ 60 minutes.
# 10. Stephanie: Pacific Heights, avail 8:45AM–5:30PM, i.e. [-15, 510], duration ≥ 105 minutes.
#
friends = [
    {"name": "Jeffrey",   "location": "Golden Gate Park",   "avail_start": 360, "avail_end": 540, "duration": 30},
    {"name": "Melissa",   "location": "Sunset District",      "avail_start": 600, "avail_end": 780, "duration": 120},
    {"name": "Andrew",    "location": "Alamo Square",         "avail_start": 75,  "avail_end": 345, "duration": 15},
    {"name": "Robert",    "location": "Embarcadero",          "avail_start": 600, "avail_end": 750, "duration": 15},
    {"name": "Laura",     "location": "Union Square",         "avail_start": 360, "avail_end": 510, "duration": 120},
    {"name": "Patricia",  "location": "Chinatown",            "avail_start": 195, "avail_end": 570, "duration": 120},
    {"name": "Margaret",  "location": "Richmond District",    "avail_start": 405, "avail_end": 765, "duration": 120},
    {"name": "George",    "location": "Marina District",      "avail_start": 570, "avail_end": 750, "duration": 60},
    {"name": "Jason",     "location": "Bayview",              "avail_start": 705, "avail_end": 765, "duration": 60},
    {"name": "Stephanie", "location": "Pacific Heights",      "avail_start": -15, "avail_end": 510, "duration": 105},
]

# ---------------------------------------------------------------------
# List of locations. (These should cover all friend locations as well as the starting point.)
locations = [
    "Russian Hill",
    "Golden Gate Park",
    "Sunset District",
    "Alamo Square",
    "Embarcadero",
    "Union Square",
    "Chinatown",
    "Richmond District",
    "Marina District",
    "Bayview",
    "Pacific Heights",
]

# ---------------------------------------------------------------------
# Travel times between locations (in minutes).
# The keys are tuples (origin, destination).
travel = {
    # From Russian Hill:
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,

    # From Golden Gate Park:
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,

    # From Sunset District:
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Pacific Heights"): 21,

    # From Alamo Square:
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,

    # From Embarcadero:
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Pacific Heights"): 11,

    # From Union Square:
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Pacific Heights"): 15,

    # From Chinatown:
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Pacific Heights"): 10,

    # From Richmond District:
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Pacific Heights"): 10,

    # From Marina District:
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Pacific Heights"): 7,

    # From Bayview:
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Pacific Heights"): 23,

    # From Pacific Heights:
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Bayview"): 22,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model
# ---------------------------------------------------------------------
# We use Optimize to maximize the number of meetings scheduled.
opt = Optimize()

num_friends = len(friends)

# Decision variables:
#   x[i]: Boolean - whether meeting with friend i is scheduled.
#   start[i]: Integer - meeting’s start time (minutes after 9:00 AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds on meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location is Russian Hill at time 0.
starting_location = "Russian Hill"
arrival_time = 0

# For each friend that is scheduled, add constraints:
#  (a) Meeting cannot start before friend’s available start.
#  (b) Meeting (start time + duration) must end by friend’s available end.
#  (c) You cannot arrive before the travel time from the starting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(starting_location, loc)
    
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(starting_location, loc)))

# Non-overlap constraints:
# For any two scheduled meetings, ensure that one meeting finishes (including travel)
# before the other begins.
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

# ---------------------------------------------------------------------
# Solve and Print the Schedule
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            t = model.evaluate(start[i]).as_long()
            schedule.append((t, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00 AM):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            total = 9 * 60 + minutes
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")