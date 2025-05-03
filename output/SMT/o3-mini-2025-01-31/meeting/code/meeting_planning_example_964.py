from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each key is a tuple (origin, destination)
travel = {
    # From North Beach
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Bayview"): 25,
    
    # From Russian Hill
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Bayview"): 23,
    
    # From Golden Gate Park
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Bayview"): 18,
    
    # From Sunset District
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Bayview"): 22,
    
    # From Presidio
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    
    # From Mission District
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 14,
    
    # From Chinatown
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Bayview"): 20,
    
    # From Alamo Square
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Bayview"): 16,
    
    # From Fisherman's Wharf
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Bayview"): 26,
    
    # From Bayview
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Fisherman's Wharf"): 25,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at North Beach at 9:00AM.
arrival_location = "North Beach"
arrival_time = 0  # minutes after 9:00AM

# Friend meeting data.
# All times are given in minutes after 9:00AM.
# (Negative values indicate times before 9:00AM.)
# The conversion:
# Amanda (at Russian Hill): 5:45PM to 9:00PM -> avail_start = 525, avail_end = 720, duration = 60
# Kenneth (at Golden Gate Park): 9:00AM to 3:45PM -> avail_start = 0, avail_end = 405, duration = 45
# Carol (at Haight-Ashbury): 7:00AM to 5:15PM -> avail_start = -120, avail_end = 495, duration = 120
# James (at Sunset District): 7:45AM to 12:30PM -> avail_start = -75, avail_end = 210, duration = 105
# Barbara (at Presidio): 10:45AM to 10:00PM -> avail_start = 105, avail_end = 780, duration = 90
# Melissa (at Mission District): 1:45PM to 5:30PM -> avail_start = 285, avail_end = 510, duration = 120
# Stephanie (at Chinatown): 9:00PM to 9:45PM -> avail_start = 720, avail_end = 765, duration = 45
# Emily (at Alamo Square): 8:00PM to 10:00PM -> avail_start = 660, avail_end = 780, duration = 120
# Ashley (at Fisherman's Wharf): 11:15AM to 2:45PM -> avail_start = 135, avail_end = 345, duration = 90
# Jessica (at Bayview): 6:45PM to 8:15PM -> avail_start = 585, avail_end = 675, duration = 60

friends = [
    {"name": "Amanda",   "location": "Russian Hill",     "avail_start": 525, "avail_end": 720, "duration": 60},
    {"name": "Kenneth",  "location": "Golden Gate Park", "avail_start": 0,   "avail_end": 405, "duration": 45},
    {"name": "Carol",    "location": "Haight-Ashbury",   "avail_start": -120,"avail_end": 495, "duration": 120},
    {"name": "James",    "location": "Sunset District",  "avail_start": -75, "avail_end": 210, "duration": 105},
    {"name": "Barbara",  "location": "Presidio",         "avail_start": 105, "avail_end": 780, "duration": 90},
    {"name": "Melissa",  "location": "Mission District", "avail_start": 285, "avail_end": 510, "duration": 120},
    {"name": "Stephanie","location": "Chinatown",        "avail_start": 720, "avail_end": 765, "duration": 45},
    {"name": "Emily",    "location": "Alamo Square",     "avail_start": 660, "avail_end": 780, "duration": 120},
    {"name": "Ashley",   "location": "Fisherman's Wharf","avail_start": 135, "avail_end": 345, "duration": 90},
    {"name": "Jessica",  "location": "Bayview",          "avail_start": 585, "avail_end": 675, "duration": 60},
]

num_friends = len(friends)

# All locations used in the problem.
locations = [
    "North Beach",
    "Russian Hill",
    "Golden Gate Park",
    "Haight-Ashbury",
    "Sunset District",
    "Presidio",
    "Mission District",
    "Chinatown",
    "Alamo Square",
    "Fisherman's Wharf",
    "Bayview",
]

# Decision variables:
# For each friend, we define:
#   x[i] : a Boolean indicating if this meeting is scheduled.
#   start[i] : an integer representing the start time of the meeting (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow start time to vary sufficiently
    opt.add(start[i] >= -300, start[i] <= 1000)

# For every meeting, if it is scheduled then:
# 1. Its start must not be before the friend's available start time.
# 2. It must finish (start + duration) by the friend's available end.
# 3. You must be able to travel from your arrival location ("North Beach") to the meeting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Non-overlap constraints:
# For any two scheduled meetings, enforce that one ends (plus travel time to the location of the other) before the other starts.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        d_i = friends[i]["duration"]
        d_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        no_overlap = Or(
            start[i] + d_i + travel_i_j <= start[j],
            start[j] + d_j + travel_j_i <= start[i]
        )
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the scheduling problem and output the results.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM):")
    def format_time(minutes_after9):
        # 9:00AM is 540 minutes after midnight
        total = 540 + minutes_after9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")