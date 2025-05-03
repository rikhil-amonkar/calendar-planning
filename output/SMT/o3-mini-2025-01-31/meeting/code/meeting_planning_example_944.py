from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are measured in minutes after 9:00AM at Mission District (time=0).

# Kimberly: at Russian Hill from 7:00AM to 10:30AM.
#   7:00AM = -120 minutes, 10:30AM = 90 minutes.
#   Minimum meeting duration: 105 minutes.
# Charles: at Chinatown from 5:45PM to 8:45PM.
#   5:45PM = 525 minutes, 8:45PM = 705 minutes.
#   Minimum meeting duration: 60 minutes.
# Matthew: at Fisherman's Wharf from 1:45PM to 5:15PM.
#   1:45PM = 285 minutes, 5:15PM = 495 minutes.
#   Minimum meeting duration: 15 minutes.
# Melissa: at Bayview from 3:45PM to 5:00PM.
#   3:45PM = 405 minutes, 5:00PM = 480 minutes.
#   Minimum meeting duration: 30 minutes.
# Carol: at Golden Gate Park from 10:00AM to 2:45PM.
#   10:00AM = 60 minutes, 2:45PM = 345 minutes.
#   Minimum meeting duration: 45 minutes.
# Nancy: at Union Square from 11:15AM to 9:00PM.
#   11:15AM = 135 minutes, 9:00PM = 720 minutes.
#   Minimum meeting duration: 75 minutes.
# Ronald: at Richmond District from 8:45AM to 9:15PM.
#   8:45AM = -15 minutes, 9:15PM = 735 minutes.
#   Minimum meeting duration: 90 minutes.
# Jeffrey: at Marina District from 12:15PM to 7:00PM.
#   12:15PM = 195 minutes, 7:00PM = 600 minutes.
#   Minimum meeting duration: 15 minutes.
# James: at The Castro from 6:45PM to 8:30PM.
#   6:45PM = 585 minutes, 8:30PM = 690 minutes.
#   Minimum meeting duration: 15 minutes.
# Laura: at Financial District from 7:45AM to 12:15PM.
#   7:45AM = -75 minutes, 12:15PM = 195 minutes.
#   Minimum meeting duration: 45 minutes.
friends = [
    {"name": "Kimberly", "location": "Russian Hill",       "avail_start": -120, "avail_end": 90,  "duration": 105},
    {"name": "Charles",   "location": "Chinatown",           "avail_start": 525,  "avail_end": 705, "duration": 60},
    {"name": "Matthew",   "location": "Fisherman's Wharf",   "avail_start": 285,  "avail_end": 495, "duration": 15},
    {"name": "Melissa",   "location": "Bayview",             "avail_start": 405,  "avail_end": 480, "duration": 30},
    {"name": "Carol",     "location": "Golden Gate Park",    "avail_start": 60,   "avail_end": 345, "duration": 45},
    {"name": "Nancy",     "location": "Union Square",        "avail_start": 135,  "avail_end": 720, "duration": 75},
    {"name": "Ronald",    "location": "Richmond District",   "avail_start": -15,  "avail_end": 735, "duration": 90},
    {"name": "Jeffrey",   "location": "Marina District",     "avail_start": 195,  "avail_end": 600, "duration": 15},
    {"name": "James",     "location": "The Castro",          "avail_start": 585,  "avail_end": 690, "duration": 15},
    {"name": "Laura",     "location": "Financial District",  "avail_start": -75,  "avail_end": 195, "duration": 45},
]

# -----------------------------------------------------------------------------
# List of locations.
# Our arrival is at Mission District at 9:00AM (time = 0).
locations = [
    "Mission District",   # Arrival location at 9:00AM.
    "Russian Hill",
    "Chinatown",
    "Fisherman's Wharf",
    "Bayview",
    "Golden Gate Park",
    "Union Square",
    "Richmond District",
    "Marina District",
    "The Castro",
    "Financial District",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Mission District:
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 15,
    
    # From Russian Hill:
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Financial District"): 11,
    
    # From Chinatown:
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Financial District"): 5,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    
    # From Bayview:
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Financial District"): 19,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Financial District"): 26,
    
    # From Union Square:
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Financial District"): 9,
    
    # From Richmond District:
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Financial District"): 22,
    
    # From Marina District:
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Financial District"): 17,
    
    # From The Castro:
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Financial District"): 21,
    
    # From Financial District:
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "The Castro"): 20,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i:
#   x[i] is a Boolean indicator of whether we schedule a meeting.
#   start[i] is an integer representing the meeting start time (minutes after 9:00AM at Mission District).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Our arrival is at Mission District at time = 0.
arrival_location = "Mission District"
arrival_time = 0

# For each scheduled friend, enforce:
#  - The meeting cannot start before the friend's available start.
#  - The meeting must finish (start + duration) by the friend's available end.
#  - The meeting start time must be no earlier than our arrival time plus travel time from Mission District to the friend's location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Pairwise non-overlap constraints:
# For any two meetings that are both scheduled, enforce that either meeting i (plus its duration and travel time from i's location to j's location)
# finishes before meeting j starts or vice versa.
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
    
    print("Optimal Schedule (times are minutes after 9:00AM at Mission District):")
    
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