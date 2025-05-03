from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# Times are measured in minutes relative to your arrival at Fisherman's Wharf at 9:00AM (time = 0).

# 0. James at Presidio from 8:15PM to 10:00PM: [675, 780], min meeting 105 minutes.
# 1. Richard at Alamo Square from 5:45PM to 7:00PM: [525, 600], min meeting 60 minutes.
# 2. Thomas at Embarcadero from 8:00PM to 10:00PM: [660, 780], min meeting 120 minutes.
# 3. Melissa at Sunset District from 11:00AM to 1:15PM: [120, 255], min meeting 105 minutes.
# 4. Andrew at Chinatown from 1:30PM to 9:00PM: [270, 720], min meeting 105 minutes.
# 5. Mary at Pacific Heights from 6:15PM to 8:00PM: [555, 660], min meeting 75 minutes.
# 6. Rebecca at Nob Hill from 7:45PM to 8:30PM: [645, 690], min meeting 30 minutes.
# 7. John at The Castro from 1:45PM to 4:30PM: [285, 450], min meeting 30 minutes.
# 8. Jeffrey at Richmond District from 3:15PM to 7:00PM: [375, 600], min meeting 60 minutes.
friends = [
    {"name": "James",    "location": "Presidio",         "avail_start": 675, "avail_end": 780, "duration": 105},
    {"name": "Richard",  "location": "Alamo Square",     "avail_start": 525, "avail_end": 600, "duration": 60},
    {"name": "Thomas",   "location": "Embarcadero",      "avail_start": 660, "avail_end": 780, "duration": 120},
    {"name": "Melissa",  "location": "Sunset District",  "avail_start": 120, "avail_end": 255, "duration": 105},
    {"name": "Andrew",   "location": "Chinatown",        "avail_start": 270, "avail_end": 720, "duration": 105},
    {"name": "Mary",     "location": "Pacific Heights",  "avail_start": 555, "avail_end": 660, "duration": 75},
    {"name": "Rebecca",  "location": "Nob Hill",         "avail_start": 645, "avail_end": 690, "duration": 30},
    {"name": "John",     "location": "The Castro",       "avail_start": 285, "avail_end": 450, "duration": 30},
    {"name": "Jeffrey",  "location": "Richmond District","avail_start": 375, "avail_end": 600, "duration": 60},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Fisherman's Wharf",
    "Presidio",
    "Alamo Square",
    "Embarcadero",
    "Sunset District",
    "Chinatown",
    "Pacific Heights",
    "Nob Hill",
    "The Castro",
    "North Beach",
    "Richmond District",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# These values are taken from the problem statement.
travel = {
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Richmond District"): 18,
    
    # From Presidio:
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Richmond District"): 7,
    
    # From Alamo Square:
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Richmond District"): 11,
    
    # From Embarcadero:
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Richmond District"): 21,
    
    # From Sunset District:
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Richmond District"): 12,
    
    # From Chinatown:
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Richmond District"): 20,
    
    # From Pacific Heights:
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Richmond District"): 12,
    
    # From Nob Hill:
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Richmond District"): 14,
    
    # From The Castro:
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Richmond District"): 16,
    
    # From North Beach:
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Richmond District"): 18,
    
    # From Richmond District:
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "North Beach"): 17,
}

# Helper function to obtain travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize() to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i:
#   x[i] is a Boolean that is True if the meeting is scheduled.
#   start[i] is an integer representing the meeting start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Give wide bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Fisherman's Wharf at 9:00AM.
arrival_location = "Fisherman's Wharf"
arrival_time = 0

# For each meeting that is scheduled, enforce:
# 1. Meeting start is no earlier than the friend's available start.
# 2. Meeting (plus its minimum duration) finishes by the available end.
# 3. There is enough time to travel from the arrival location to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Pairwise non-overlap constraints:
# For any two scheduled meetings i and j, ensure that one finishes (including travel time to the next) before the other begins.
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
# Solve and print the scheduled itinerary.
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            t_val = model.evaluate(start[i]).as_long()
            schedule.append((t_val, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM at Fisherman's Wharf):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            # Convert minutes relative to 9:00AM to HH:MM format.
            total = 540 + minutes  # 9:00AM is 540 minutes after midnight.
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")