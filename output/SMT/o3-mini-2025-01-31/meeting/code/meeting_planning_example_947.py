from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Russian Hill:
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Alamo Square"): 15,
    
    # From North Beach:
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    
    # From Sunset District:
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    
    # From Marina District:
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Alamo Square"): 15,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Alamo Square"): 9,
    
    # From Embarcadero:
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Alamo Square"): 19,
    
    # From Nob Hill:
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Alamo Square"): 11,
    
    # From Bayview:
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Alamo Square"): 16,
    
    # From Union Square:
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Alamo Square"): 15,
    
    # From Alamo Square:
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Union Square"): 14,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
# Our time units are in minutes after 9:00AM.
# Arrival location: Russian Hill at 9:00AM (time=0).
opt = Optimize()
num_friends = 9

# Define friend meeting constraints.
# Times (minutes after 9:00AM):
# - Stephanie: at North Beach from 1:15PM to 5:15PM.
#     1:15PM = 255, 5:15PM = 555, duration: 90 minutes.
# - Andrew: at Sunset District from 8:00PM to 9:45PM.
#     8:00PM = 660, 9:45PM = 705, duration: 105 minutes.
# - Richard: at Marina District from 12:00PM to 6:00PM.
#     12:00PM = 180, 6:00PM = 540, duration: 120 minutes.
# - Ronald: at Fisherman's Wharf from 7:00PM to 9:30PM.
#     7:00PM = 600, 9:30PM = 750, duration: 120 minutes.
# - Jason: at Golden Gate Park from 1:00PM to 4:45PM.
#     1:00PM = 240, 4:45PM = 465, duration: 15 minutes.
# - Melissa: at Embarcadero from 3:30PM to 10:00PM.
#     3:30PM = 390, 10:00PM = 780, duration: 60 minutes.
# - Robert: at Nob Hill from 3:00PM to 8:30PM.
#     3:00PM = 360, 8:30PM = 690, duration: 75 minutes.
# - Emily: at Bayview from 11:15AM to 7:15PM.
#     11:15AM = 135, 7:15PM = 615, duration: 15 minutes.
# - Mary: at Union Square from 1:45PM to 2:45PM.
#     1:45PM = 285, 2:45PM = 345, duration: 60 minutes.
# - Joshua: at Alamo Square from 4:15PM to 8:45PM.
#     4:15PM = 435, 8:45PM = 705, duration: 105 minutes.

friends = [
    {"name": "Stephanie", "location": "North Beach",       "avail_start": 255, "avail_end": 555, "duration": 90},
    {"name": "Andrew",    "location": "Sunset District",     "avail_start": 660, "avail_end": 705, "duration": 105},
    {"name": "Richard",   "location": "Marina District",     "avail_start": 180, "avail_end": 540, "duration": 120},
    {"name": "Ronald",    "location": "Fisherman's Wharf",   "avail_start": 600, "avail_end": 750, "duration": 120},
    {"name": "Jason",     "location": "Golden Gate Park",    "avail_start": 240, "avail_end": 465, "duration": 15},
    {"name": "Melissa",   "location": "Embarcadero",         "avail_start": 390, "avail_end": 780, "duration": 60},
    {"name": "Robert",    "location": "Nob Hill",            "avail_start": 360, "avail_end": 690, "duration": 75},
    {"name": "Emily",     "location": "Bayview",             "avail_start": 135, "avail_end": 615, "duration": 15},
    {"name": "Mary",      "location": "Union Square",        "avail_start": 285, "avail_end": 345, "duration": 60},
    {"name": "Joshua",    "location": "Alamo Square",        "avail_start": 435, "avail_end": 705, "duration": 105},
]

# Note: Although the problem statement lists 9 friends, we have 10 entries.
# In this case, the array 'friends' has 10 entries. Adjust the number accordingly.
num_friends = len(friends)

# List of all locations.
locations = [
    "Russian Hill",       # Arrival location at 9:00AM.
    "North Beach",
    "Sunset District",
    "Marina District",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "Embarcadero",
    "Nob Hill",
    "Bayview",
    "Union Square",
    "Alamo Square",
]

# Decision variables:
# For each friend i:
#   x[i] is a Boolean indicator whether the meeting is scheduled.
#   start[i] is an integer for the meeting start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # broad domain for meeting start times
    opt.add(start[i] >= -300, start[i] <= 1000)

# Our arrival: Russian Hill at 9:00AM (time=0).
arrival_location = "Russian Hill"
arrival_time = 0

# For every scheduled friend, ensure:
# - Meeting cannot start before the friend is available.
# - Meeting (start time + duration) must finish by friend’s available end.
# - We have enough travel time from our arrival (Russian Hill) to the friend's location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Add non-overlap constraints:
# For any two scheduled meetings, ensure that one finishes (including travel time to the other's location)
# before the other starts.
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
    # Sort meetings by start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM):")
    
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