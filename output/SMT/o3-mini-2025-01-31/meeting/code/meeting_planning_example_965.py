from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Keys are tuples (origin, destination)
travel = {
    # From North Beach
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Presidio"): 17,
    
    # From Chinatown
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Presidio"): 19,
    
    # From Russian Hill
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Presidio"): 14,
    
    # From Marina District
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Presidio"): 10,
    
    # From Financial District
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Presidio"): 22,
    
    # From Nob Hill
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Presidio"): 17,
    
    # From Alamo Square
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    
    # From Mission District
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Presidio"): 25,
    
    # From The Castro
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Presidio"): 20,
    
    # From Union Square
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Presidio"): 24,
    
    # From Presidio
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Union Square"): 22,
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
# Times are defined as minutes after 9:00AM.
# (Negative values indicate times before 9:00AM.)
# Jeffrey  (Chinatown): 7:45PM to 9:45PM -> avail: [645, 765], duration = 60 minutes.
# James    (Russian Hill): 9:45AM to 7:15PM -> avail: [45, 615], duration = 15 minutes.
# Helen    (Marina District): 11:15AM to 2:00PM -> avail: [135, 300], duration = 45 minutes.
# Andrew   (Financial District): 8:15AM to 10:30AM -> avail: [-45, 90], duration = 75 minutes.
# Rebecca  (Nob Hill): 7:00AM to 8:15PM -> avail: [-120, 675], duration = 60 minutes.
# Laura    (Alamo Square): 9:45AM to 3:45PM -> avail: [45, 405], duration = 30 minutes.
# Thomas   (Mission District): 12:45PM to 2:15PM -> avail: [225, 315], duration = 60 minutes.
# Patricia (The Castro): 6:00PM to 8:30PM -> avail: [540, 690], duration = 120 minutes.
# Michelle (Union Square): 10:45AM to 6:45PM -> avail: [105, 585], duration = 120 minutes.
# Barbara  (Presidio): 12:45PM to 3:30PM -> avail: [225, 390], duration = 30 minutes.
friends = [
    {"name": "Jeffrey",  "location": "Chinatown",         "avail_start": 645, "avail_end": 765, "duration": 60},
    {"name": "James",    "location": "Russian Hill",       "avail_start": 45,  "avail_end": 615, "duration": 15},
    {"name": "Helen",    "location": "Marina District",    "avail_start": 135, "avail_end": 300, "duration": 45},
    {"name": "Andrew",   "location": "Financial District", "avail_start": -45, "avail_end": 90,  "duration": 75},
    {"name": "Rebecca",  "location": "Nob Hill",           "avail_start": -120,"avail_end": 675, "duration": 60},
    {"name": "Laura",    "location": "Alamo Square",       "avail_start": 45,  "avail_end": 405, "duration": 30},
    {"name": "Thomas",   "location": "Mission District",   "avail_start": 225, "avail_end": 315, "duration": 60},
    {"name": "Patricia", "location": "The Castro",         "avail_start": 540, "avail_end": 690, "duration": 120},
    {"name": "Michelle", "location": "Union Square",       "avail_start": 105, "avail_end": 585, "duration": 120},
    {"name": "Barbara",  "location": "Presidio",           "avail_start": 225, "avail_end": 390, "duration": 30},
]

num_friends = len(friends)

# All locations used.
locations = [
    "North Beach", "Chinatown", "Russian Hill", "Marina District",
    "Financial District", "Nob Hill", "Alamo Square", "Mission District",
    "The Castro", "Union Square", "Presidio",
]

# Decision variables:
# For each friend, x[i] denotes if the meeting is scheduled while start[i] is the meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow a wide range of start times
    opt.add(start[i] >= -300, start[i] <= 1000)

# For every meeting that is scheduled, enforce:
#   1. The meeting start is not before the friend’s available start.
#   2. The meeting finishes (start + duration) by the friend’s available end.
#   3. You have sufficient time to travel from your arrival location (North Beach) to the meeting location.
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
# For any two scheduled meetings, ensure that one meeting's end plus the travel time to the second meeting
# is no later than the second meeting's start time.
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
        # 9:00AM is 540 minutes after midnight.
        total = 540 + minutes_after9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")