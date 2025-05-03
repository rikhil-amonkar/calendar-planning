from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are in minutes relative to your arrival at Union Square at 9:00AM.
#
# Convert the clock times as follows:
# Kevin: at Mission District from 8:45PM to 9:45PM 
#        8:45PM = 20:45, which is 11h45m after 9:00AM → 705 minutes.
#        9:45PM = 21:45 → 765 minutes.
#        Minimum duration = 60 minutes.
#
# Mark: at Fisherman's Wharf from 5:15PM to 8:00PM
#       5:15PM = 17:15 → 495 minutes; 8:00PM = 20:00 → 660 minutes.
#       Minimum duration = 90 minutes.
#
# Jessica: at Russian Hill from 9:00AM to 3:00PM 
#          9:00AM = 0 minutes; 3:00PM = 360 minutes.
#          Minimum duration = 120 minutes.
#
# Jason: at Marina District from 3:15PM to 9:45PM 
#        3:15PM = 375 minutes; 9:45PM = 765 minutes.
#        Minimum duration = 120 minutes.
#
# John: at North Beach from 9:45AM to 6:00PM
#       9:45AM = 45 minutes; 6:00PM = 540 minutes.
#       Minimum duration = 15 minutes.
#
# Karen: at Chinatown from 4:45PM to 7:00PM
#        4:45PM = 465 minutes; 7:00PM = 600 minutes.
#        Minimum duration = 75 minutes.
#
# Sarah: at Pacific Heights from 5:30PM to 6:15PM
#        5:30PM = 510 minutes; 6:15PM = 555 minutes.
#        Minimum duration = 45 minutes.
#
# Amanda: at The Castro from 8:00PM to 9:15PM
#         8:00PM = 660 minutes; 9:15PM = 735 minutes.
#         Minimum duration = 60 minutes.
#
# Nancy: at Nob Hill from 9:45AM to 1:00PM
#        9:45AM = 45 minutes; 1:00PM = 240 minutes.
#        Minimum duration = 45 minutes.
#
# Rebecca: at Sunset District from 8:45AM to 3:00PM
#          8:45AM = -15 minutes (since arrival is 9:00AM) and 3:00PM = 360 minutes.
#          Minimum duration = 75 minutes.
friends = [
    {"name": "Kevin",    "location": "Mission District",  "avail_start": 705, "avail_end": 765, "duration": 60},
    {"name": "Mark",     "location": "Fisherman's Wharf", "avail_start": 495, "avail_end": 660, "duration": 90},
    {"name": "Jessica",  "location": "Russian Hill",      "avail_start": 0,   "avail_end": 360, "duration": 120},
    {"name": "Jason",    "location": "Marina District",   "avail_start": 375, "avail_end": 765, "duration": 120},
    {"name": "John",     "location": "North Beach",       "avail_start": 45,  "avail_end": 540, "duration": 15},
    {"name": "Karen",    "location": "Chinatown",         "avail_start": 465, "avail_end": 600, "duration": 75},
    {"name": "Sarah",    "location": "Pacific Heights",   "avail_start": 510, "avail_end": 555, "duration": 45},
    {"name": "Amanda",   "location": "The Castro",        "avail_start": 660, "avail_end": 735, "duration": 60},
    {"name": "Nancy",    "location": "Nob Hill",          "avail_start": 45,  "avail_end": 240, "duration": 45},
    {"name": "Rebecca",  "location": "Sunset District",   "avail_start": -15, "avail_end": 360, "duration": 75},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Union Square",      # Arrival location: you arrive here at 9:00AM.
    "Mission District",
    "Fisherman's Wharf",
    "Russian Hill",
    "Marina District",
    "North Beach",
    "Chinatown",
    "Pacific Heights",
    "The Castro",
    "Nob Hill",
    "Sunset District",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Union Square:
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    
    # From Mission District:
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Sunset District"): 24,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Sunset District"): 27,
    
    # From Russian Hill:
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    
    # From Marina District:
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    
    # From North Beach:
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    
    # From Chinatown:
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    
    # From Pacific Heights:
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Sunset District"): 21,
    
    # From The Castro:
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Sunset District"): 17,
    
    # From Nob Hill:
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 24,
    
    # From Sunset District:
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Nob Hill"): 27,
}

# Helper function to return the travel time from an origin to a destination.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i] is a Boolean which is True if meeting friend i is scheduled.
#   start[i] is an integer representing the start time (minutes after 9:00AM at Union Square) for friend i.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow a wide range for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Union Square at t = 0.
arrival_location = "Union Square"
arrival_time = 0

# For each friend, if the meeting is scheduled then:
# - The meeting start must be no earlier than the friend's available start.
# - The meeting must finish (start + duration) by the friend's available end.
# - In addition, you must have time to travel from your arrival location (Union Square) to the friend's location.
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
# For any two scheduled meetings, ensure that the meeting times (including the travel time from one meeting location to the other)
# do not overlap. That is, either meeting i finishes and you travel to meeting j before it begins,
# or vice versa.
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
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    # Sort scheduled meetings by start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Union Square):")
    # Helper to convert minutes after 9:00AM into HH:MM format (assuming 9:00AM = 540 minutes after midnight).
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