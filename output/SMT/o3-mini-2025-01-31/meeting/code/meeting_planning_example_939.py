from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are in minutes relative to 9:00AM at Fisherman's Wharf (time = 0).
# Convert the provided clock times to minutes after 9:00AM:
# Ronald (at Haight-Ashbury): 1:30PM to 2:45PM  --> [270, 345], minimum duration = 30.
# Charles (at North Beach):     5:00PM to 7:30PM  --> [480, 630], minimum duration = 75.
# Lisa (at Union Square):       3:30PM to 8:30PM  --> [390, 690], minimum duration = 75.
# James (at Sunset District):   7:00AM to 9:00PM  --> [-120, 720], minimum duration = 120.
# Richard (at Alamo Square):    9:00PM to 10:00PM --> [720, 780], minimum duration = 15.
# Kenneth (at Russian Hill):    11:00AM to 3:45PM --> [120, 405], minimum duration = 75.
# Ashley (at Financial District): 7:30PM to 9:00PM--> [630, 720], minimum duration = 15.
# Thomas (at Golden Gate Park): 7:30PM to 9:45PM  --> [630, 765], minimum duration = 75.
# Amanda (at Chinatown):        3:45PM to 6:30PM  --> [405, 570], minimum duration = 30.
# Laura (at Mission District):  12:45PM to 4:15PM --> [225, 435], minimum duration = 90.
friends = [
    {"name": "Ronald",   "location": "Haight-Ashbury",      "avail_start": 270, "avail_end": 345, "duration": 30},
    {"name": "Charles",  "location": "North Beach",         "avail_start": 480, "avail_end": 630, "duration": 75},
    {"name": "Lisa",     "location": "Union Square",        "avail_start": 390, "avail_end": 690, "duration": 75},
    {"name": "James",    "location": "Sunset District",     "avail_start": -120,"avail_end": 720, "duration": 120},
    {"name": "Richard",  "location": "Alamo Square",        "avail_start": 720, "avail_end": 780, "duration": 15},
    {"name": "Kenneth",  "location": "Russian Hill",        "avail_start": 120, "avail_end": 405, "duration": 75},
    {"name": "Ashley",   "location": "Financial District",  "avail_start": 630, "avail_end": 720, "duration": 15},
    {"name": "Thomas",   "location": "Golden Gate Park",    "avail_start": 630, "avail_end": 765, "duration": 75},
    {"name": "Amanda",   "location": "Chinatown",           "avail_start": 405, "avail_end": 570, "duration": 30},
    {"name": "Laura",    "location": "Mission District",    "avail_start": 225, "avail_end": 435, "duration": 90},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Fisherman's Wharf",  # your starting/arrival location at 9:00AM.
    "Haight-Ashbury",
    "North Beach",
    "Union Square",
    "Sunset District",
    "Alamo Square",
    "Russian Hill",
    "Financial District",
    "Golden Gate Park",
    "Chinatown",
    "Mission District",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# These distances are directional.
travel = {
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Mission District"): 11,
    
    # From North Beach:
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Mission District"): 18,
    
    # From Union Square:
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    
    # From Sunset District:
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 25,
    
    # From Alamo Square:
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Mission District"): 10,
    
    # From Russian Hill:
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Mission District"): 16,
    
    # From Financial District:
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Mission District"): 17,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    
    # From Chinatown:
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Mission District"): 17,
    
    # From Mission District:
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
}

# Helper function that returns the travel time from an origin to a destination.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i] is a Boolean indicating whether we schedule a meeting with friend i.
#   start[i] is an integer representing the start time (in minutes from 9:00AM at Fisherman's Wharf).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Fisherman's Wharf at time = 0.
arrival_location = "Fisherman's Wharf"
arrival_time = 0

# For each friend, if the meeting is scheduled then:
# - The meeting must start no earlier than the friend's available start.
# - The meeting must finish (start + duration) no later than the friend's available end.
# - Additionally, you must have time to travel from your starting location (Fisherman's Wharf) to the friend's location.
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
# For any two scheduled meetings, ensure that after finishing one meeting and traveling to the next location,
# the next meeting does not start until that travel is complete.
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
# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    # Gather scheduled meetings.
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    # Sort meetings by start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Fisherman's Wharf):")
    # Helper to convert minutes after 9:00AM into HH:MM format (with 9:00AM as 540 minutes after midnight).
    def format_time(m):
        total = 540 + m
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")