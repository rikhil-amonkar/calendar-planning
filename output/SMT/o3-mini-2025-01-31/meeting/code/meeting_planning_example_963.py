from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations, given as a dictionary.
# The key is a tuple (origin, destination).
travel = {
    # From North Beach
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Presidio"): 17,
    
    # From Marina District
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,
    
    # From Union Square
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    
    # From Mission District
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Presidio"): 25,
    
    # From Financial District
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    
    # From Russian Hill
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    
    # From Pacific Heights
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Presidio"): 11,
    
    # From Fisherman's Wharf
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Presidio"): 17,
    
    # From Sunset District
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Presidio"): 16,
    
    # From Alamo Square
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 17,
    
    # From Presidio
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 19,
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
# All times are defined as minutes after 9:00AM.
# (Negative values indicate times before 9:00AM.)
# The following conversions are used:
# Linda: 8:45AM to 11:30AM  --> avail_start = -15, avail_end = 150, min duration = 105.
# Andrew: 7:45AM to 6:45PM   --> avail_start = -75, avail_end = 585, min duration = 15.
# Laura: 4:15PM to 5:45PM     --> avail_start = 435, avail_end = 525, min duration = 30.
# Thomas: 1:30PM to 6:45PM    --> avail_start = 270, avail_end = 585, min duration = 120.
# Kevin: 7:45PM to 8:30PM     --> avail_start = 645, avail_end = 690, min duration = 30.
# William: 11:45AM to 2:00PM  --> avail_start = 165, avail_end = 300, min duration = 30.
# Lisa: 10:45AM to 2:15PM     --> avail_start = 105, avail_end = 315, min duration = 30.
# James: 7:00AM to 1:45PM     --> avail_start = -120, avail_end = 285, min duration = 105.
# Ronald: 7:15AM to 12:45PM   --> avail_start = -105, avail_end = 225, min duration = 45.
# Michelle: 10:45AM to 2:30PM  --> avail_start = 105, avail_end = 330, min duration = 105.
friends = [
    {"name": "Linda",    "location": "Marina District",    "avail_start": -15,  "avail_end": 150,  "duration": 105},
    {"name": "Andrew",   "location": "Union Square",       "avail_start": -75,  "avail_end": 585,  "duration": 15},
    {"name": "Laura",    "location": "Mission District",   "avail_start": 435,  "avail_end": 525,  "duration": 30},
    {"name": "Thomas",   "location": "Financial District", "avail_start": 270,  "avail_end": 585,  "duration": 120},
    {"name": "Kevin",    "location": "Russian Hill",       "avail_start": 645,  "avail_end": 690,  "duration": 30},
    {"name": "William",  "location": "Pacific Heights",    "avail_start": 165,  "avail_end": 300,  "duration": 30},
    {"name": "Lisa",     "location": "Fisherman's Wharf",  "avail_start": 105,  "avail_end": 315,  "duration": 30},
    {"name": "James",    "location": "Sunset District",    "avail_start": -120, "avail_end": 285,  "duration": 105},
    {"name": "Ronald",   "location": "Alamo Square",       "avail_start": -105, "avail_end": 225,  "duration": 45},
    {"name": "Michelle", "location": "Presidio",           "avail_start": 105,  "avail_end": 330,  "duration": 105},
]

num_friends = len(friends)

# List of locations used.
locations = [
    "North Beach",
    "Marina District",
    "Union Square",
    "Mission District",
    "Financial District",
    "Russian Hill",
    "Pacific Heights",
    "Fisherman's Wharf",
    "Sunset District",
    "Alamo Square",
    "Presidio",
]

# Decision variables:
# For each friend i, create:
#   x[i]: a Boolean that denotes if the meeting is scheduled.
#   start[i]: an integer representing the meeting's start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, add constraints:
# 1. The meeting must not start before the friend's available start.
# 2. The meeting must finish (i.e. start + duration) by the friend's available end.
# 3. You must be able to travel from your arrival location (North Beach) in time.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Add non-overlap constraints.
# For any two meetings that are both scheduled, ensure that one ends (plus travel time
# to the next meeting's location) before the other begins.
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
# Solve the scheduling problem and output the itinerary.
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
        # 9:00AM = 540 minutes after midnight.
        total = 540 + minutes_after9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")