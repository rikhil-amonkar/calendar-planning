from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Sunset District:
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    # From Bayview:
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Russian Hill"): 23,
    # From Alamo Square:
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,
    # From Pacific Heights:
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Russian Hill"): 7,
    # From Financial District:
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    # From Embarcadero:
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Russian Hill"): 8,
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    # From Marina District:
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    # From Mission District:
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,
    # From Nob Hill:
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Russian Hill"): 5,
    # From Russian Hill:
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Nob Hill"): 5,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
# We use time units in minutes after 9:00AM at Sunset District (arrival time = 0).
opt = Optimize()
num_friends = 10

# Friend definitions:
# Times (in minutes after 9:00AM):
# James: Bayview from 12:45PM to 4:00PM --> [225, 420], minimum duration 15 minutes.
# Timothy: Alamo Square from 12:30PM to 6:30PM --> [210, 570], minimum duration 15 minutes.
# Patricia: Pacific Heights from 8:45PM to 10:00PM --> [705, 780], minimum duration 45 minutes.
# Sarah: Financial District from 1:15PM to 7:15PM --> [255, 615], minimum duration 90 minutes.
# Sandra: Embarcadero from 3:15PM to 10:00PM --> [375, 780], minimum duration 90 minutes.
# Andrew: Haight-Ashbury from 6:00PM to 8:15PM --> [540, 675], minimum duration 60 minutes.
# Deborah: Marina District from 3:15PM to 7:15PM --> [375, 615], minimum duration 90 minutes.
# Steven: Mission District from 6:15PM to 8:30PM --> [555, 690], minimum duration 105 minutes.
# Karen: Nob Hill from 9:30AM to 4:30PM --> [30, 450], minimum duration 90 minutes.
# Robert: Russian Hill from 7:45PM to 9:45PM --> [645, 765], minimum duration 120 minutes.
friends = [
    {"name": "James",    "location": "Bayview",          "avail_start": 225, "avail_end": 420, "duration": 15},
    {"name": "Timothy",  "location": "Alamo Square",     "avail_start": 210, "avail_end": 570, "duration": 15},
    {"name": "Patricia", "location": "Pacific Heights",  "avail_start": 705, "avail_end": 780, "duration": 45},
    {"name": "Sarah",    "location": "Financial District","avail_start": 255, "avail_end": 615, "duration": 90},
    {"name": "Sandra",   "location": "Embarcadero",      "avail_start": 375, "avail_end": 780, "duration": 90},
    {"name": "Andrew",   "location": "Haight-Ashbury",   "avail_start": 540, "avail_end": 675, "duration": 60},
    {"name": "Deborah",  "location": "Marina District",  "avail_start": 375, "avail_end": 615, "duration": 90},
    {"name": "Steven",   "location": "Mission District", "avail_start": 555, "avail_end": 690, "duration": 105},
    {"name": "Karen",    "location": "Nob Hill",         "avail_start": 30,  "avail_end": 450, "duration": 90},
    {"name": "Robert",   "location": "Russian Hill",     "avail_start": 645, "avail_end": 765, "duration": 120},
]

# List of locations.
locations = [
    "Sunset District",  # Arrival location at 9:00AM.
    "Bayview",
    "Alamo Square",
    "Pacific Heights",
    "Financial District",
    "Embarcadero",
    "Haight-Ashbury",
    "Marina District",
    "Mission District",
    "Nob Hill",
    "Russian Hill",
]

# Decision variables:
# For each friend i:
#   x[i] is a Boolean indicator: True if we schedule a meeting.
#   start[i] is an integer representing the meeting start time (minutes after 9:00AM at Sunset District).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)  # a broad time window

# Our arrival is at Sunset District at time = 0.
arrival_location = "Sunset District"
arrival_time = 0

# For every scheduled friend, ensure:
#   - The meeting starts at or after the friend's available start.
#   - The meeting ends (start + duration) by the friend's available end.
#   - We have enough travel time from our arrival point to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For any two scheduled meetings, add non-overlap constraints.
# That is, if meetings i and j are both scheduled then either meeting i (plus its duration
# and travel time from its location to j’s location) finishes before meeting j starts,
# or vice versa.
for i in range(num_friends):
    for j in range(i + 1, num_friends):
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
    # Sort the meetings by start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Sunset District):")
    
    def format_time(m):
        # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) into HH:MM.
        total = 540 + m
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")