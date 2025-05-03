from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
#
# Times are in minutes relative to 9:00AM (time==0).
#
# 1. Mark at Golden Gate Park from 10:00AM to 6:30PM:
#    [60, 570] minutes, minimum meeting duration 105 minutes.
# 2. Melissa at Russian Hill from 7:15AM to 6:00PM:
#    [ -105, 540 ] minutes, minimum meeting duration 45 minutes.
# 3. Robert at Fisherman's Wharf from 4:45PM to 8:30PM:
#    [465, 690] minutes, minimum meeting duration 60 minutes.
# 4. Andrew at Chinatown from 7:00AM to 11:15AM:
#    [-120, 135] minutes, minimum meeting duration 105 minutes.
# 5. Betty at Alamo Square from 10:00AM to 8:30PM:
#    [60, 690] minutes, minimum meeting duration 75 minutes.
# 6. Lisa at Financial District from 8:30AM to 12:00PM:
#    [-30, 180] minutes, minimum meeting duration 45 minutes.
# 7. Matthew at Sunset District from 8:00PM to 10:00PM:
#    [660, 780] minutes, minimum meeting duration 75 minutes.
# 8. Kevin at Bayview from 8:30AM to 1:15PM:
#    [-30, 255] minutes, minimum meeting duration 105 minutes.
# 9. Jessica at Pacific Heights from 9:15AM to 5:30PM:
#    [15, 510] minutes, minimum meeting duration 120 minutes.
# 10. Amanda at Presidio from 7:30PM to 9:30PM:
#    [630, 750] minutes, minimum meeting duration 120 minutes.
friends = [
    {"name": "Mark",     "location": "Golden Gate Park",   "avail_start": 60,   "avail_end": 570, "duration": 105},
    {"name": "Melissa",  "location": "Russian Hill",       "avail_start": -105, "avail_end": 540, "duration": 45},
    {"name": "Robert",   "location": "Fisherman's Wharf",  "avail_start": 465,  "avail_end": 690, "duration": 60},
    {"name": "Andrew",   "location": "Chinatown",          "avail_start": -120, "avail_end": 135, "duration": 105},
    {"name": "Betty",    "location": "Alamo Square",       "avail_start": 60,   "avail_end": 690, "duration": 75},
    {"name": "Lisa",     "location": "Financial District", "avail_start": -30,  "avail_end": 180, "duration": 45},
    {"name": "Matthew",  "location": "Sunset District",    "avail_start": 660,  "avail_end": 780, "duration": 75},
    {"name": "Kevin",    "location": "Bayview",            "avail_start": -30,  "avail_end": 255, "duration": 105},
    {"name": "Jessica",  "location": "Pacific Heights",    "avail_start": 15,   "avail_end": 510, "duration": 120},
    {"name": "Amanda",   "location": "Presidio",           "avail_start": 630,  "avail_end": 750, "duration": 120},
]

# ---------------------------------------------------------------------
# List of locations (includes all meeting places plus the starting point).
locations = [
    "Marina District",
    "Golden Gate Park",
    "Russian Hill",
    "Fisherman's Wharf",
    "Chinatown",
    "Alamo Square",
    "Financial District",
    "Sunset District",
    "Bayview",
    "Pacific Heights",
    "Presidio"
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# Keys are tuples (origin, destination).
travel = {
    # From Marina District:
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Presidio"): 10,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    
    # From Russian Hill:
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Presidio"): 14,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Presidio"): 17,
    
    # From Chinatown:
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Presidio"): 19,
    
    # From Alamo Square:
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Presidio"): 17,
    
    # From Financial District:
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Presidio"): 22,
    
    # From Sunset District:
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Bayview"): 23,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Presidio"): 16,
    
    # From Bayview:
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Presidio"): 32,
    
    # From Pacific Heights:
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Presidio"): 11,
    
    # From Presidio:
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Pacific Heights"): 11,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model
# ---------------------------------------------------------------------
# We use Optimize to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i] is True if meeting with friend i is scheduled.
#   start[i] is the start time (in minutes after 9:00AM) of the meeting.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set loose bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location is Marina District at time 0.
starting_location = "Marina District"
arrival_time = 0

# For each friend scheduled, add constraints:
# (a) The meeting must not start before the friend’s availability.
# (b) The meeting must finish (start time + duration) by the available end.
# (c) The meeting cannot start until you have traveled from the starting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(starting_location, loc)
    
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Non-overlap constraints:
# For every pair of scheduled meetings, ensure that one meeting (plus travel time)
# finishes before the other begins.
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

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the schedule.
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            t = model.evaluate(start[i]).as_long()
            schedule.append((t, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            total = 9 * 60 + minutes
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")