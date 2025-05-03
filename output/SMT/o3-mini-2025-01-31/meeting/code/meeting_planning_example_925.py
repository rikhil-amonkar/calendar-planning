from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# Times are expressed in minutes relative to your arrival at Presidio at 9:00AM (time = 0).
# Conversions:
#   Timothy: 3:15PM -> 375, 9:45PM -> 765, min duration = 105 minutes.
#   Kenneth: 3:00PM -> 360, 5:45PM -> 525, min duration = 45 minutes.
#   Michelle: 1:45PM -> 285, 2:45PM -> 345, min duration = 15 minutes.
#   Jessica: 6:15PM -> 555, 8:00PM -> 660, min duration = 90 minutes.
#   Elizabeth: 12:30PM -> 210, 2:30PM -> 330, min duration = 120 minutes.
#   Karen: 11:45AM -> 165, 8:30PM -> 690, min duration = 15 minutes.
#   Joshua: 12:45PM -> 225, 2:45PM -> 345, min duration = 75 minutes.
#   Mary: 4:00PM -> 420, 5:45PM -> 525, min duration = 30 minutes.
#   Ronald: 4:30PM -> 450, 9:30PM -> 750, min duration = 60 minutes.
#   John: 9:30AM -> 30, 12:00PM -> 180, min duration = 15 minutes.
friends = [
    {"name": "Timothy",   "location": "Nob Hill",           "avail_start": 375, "avail_end": 765, "duration": 105},
    {"name": "Kenneth",   "location": "Chinatown",          "avail_start": 360, "avail_end": 525, "duration": 45},
    {"name": "Michelle",  "location": "Fisherman's Wharf",  "avail_start": 285, "avail_end": 345, "duration": 15},
    {"name": "Jessica",   "location": "Marina District",    "avail_start": 555, "avail_end": 660, "duration": 90},
    {"name": "Elizabeth", "location": "Mission District",   "avail_start": 210, "avail_end": 330, "duration": 120},
    {"name": "Karen",     "location": "Embarcadero",        "avail_start": 165, "avail_end": 690, "duration": 15},
    {"name": "Joshua",    "location": "Alamo Square",       "avail_start": 225, "avail_end": 345, "duration": 75},
    {"name": "Mary",      "location": "Financial District", "avail_start": 420, "avail_end": 525, "duration": 30},
    {"name": "Ronald",    "location": "Russian Hill",       "avail_start": 450, "avail_end": 750, "duration": 60},
    {"name": "John",      "location": "Golden Gate Park",   "avail_start": 30,  "avail_end": 180, "duration": 15},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Presidio",
    "Nob Hill",
    "Chinatown",
    "Fisherman's Wharf",
    "Marina District",
    "Mission District",
    "Embarcadero",
    "Alamo Square",
    "Financial District",
    "Russian Hill",
    "Golden Gate Park",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# These distances are provided in the problem statement.
travel = {
    # From Presidio:
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Golden Gate Park"): 12,
    
    # From Nob Hill:
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Golden Gate Park"): 17,
    
    # From Chinatown:
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    
    # From Marina District:
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Golden Gate Park"): 18,
    
    # From Mission District:
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    
    # From Embarcadero:
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Golden Gate Park"): 25,
    
    # From Alamo Square:
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    
    # From Financial District:
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Golden Gate Park"): 23,
    
    # From Russian Hill:
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Russian Hill"): 19,
}

# Helper function to retrieve travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize() to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i] is a Boolean variable indicating if we schedule a meeting with friend i.
# start[i] is an integer variable representing the meeting's start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Give wide bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Presidio at 9:00AM.
arrival_location = "Presidio"
arrival_time = 0

# For each meeting that is scheduled, enforce:
#   1. The meeting does not start before the friend’s available start.
#   2. The meeting (plus its duration) finishes by the friend’s available end.
#   3. The meeting doesn't begin before there is enough travel time from Presidio.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Pairwise non-overlap constraints:
# For any two meetings that are both scheduled, enforce that one meeting finishes (plus travel time to the next location)
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
    
    print("Optimal schedule (times in minutes after 9:00AM at Presidio):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            # Convert minutes after 9:00AM (where 9:00AM = 540 minutes after midnight) to HH:MM format.
            total = 540 + minutes
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")