from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes). The keys are (origin, destination) pairs.
travel = {
    # From Richmond District:
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Mission District"): 20,
    
    # From Nob Hill:
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Mission District"): 13,
    
    # From Russian Hill:
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Mission District"): 16,
    
    # From Embarcadero:
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Mission District"): 20,
    
    # From Union Square:
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Mission District"): 14,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Mission District"): 17,
    
    # From The Castro:
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Mission District"): 7,
    
    # From Alamo Square:
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Mission District"): 10,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Mission District"): 22,
    
    # From Sunset District:
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Mission District"): 25,
    
    # From Mission District:
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Sunset District"): 24,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimization model.
opt = Optimize()

# You arrive at Richmond District at 9:00AM.
arrival_location = "Richmond District"
arrival_time = 0  # minutes after 9:00AM

# Friends meeting parameters.
# All times are in minutes after 9:00AM.
#   Betty: at Nob Hill from 1:30PM to 3:00PM.
#          1:30PM - 9:00AM = 4.5 hrs = 270; 3:00PM = 360; duration = 15 minutes.
#   Margaret: at Russian Hill from 11:30AM to 4:45PM.
#          11:30AM = 150; 4:45PM = 465; duration = 45 minutes.
#   Mary: at Embarcadero from 9:00AM to 3:00PM.
#          [0, 360]; duration = 90 minutes.
#   Jessica: at Union Square from 8:45AM to 5:15PM.
#          8:45AM = -15; 5:15PM = 495; duration = 15 minutes.
#   Stephanie: at Golden Gate Park from 1:30PM to 4:15PM.
#          [270, 435]; duration = 45 minutes.
#   Paul: at The Castro from 2:30PM to 5:45PM.
#          2:30PM = 330; 5:45PM = 525; duration = 90 minutes.
#   Laura: at Alamo Square from 5:45PM to 9:30PM.
#          5:45PM = 525; 9:30PM = 750; duration = 105 minutes.
#   Deborah: at Fisherman's Wharf from 11:45AM to 7:45PM.
#          11:45AM = 165; 7:45PM = 645; duration = 75 minutes.
#   Richard: at Sunset District from 11:45AM to 1:45PM.
#          [165, 285]; duration = 15 minutes.
#   Kenneth: at Mission District from 11:00AM to 9:30PM.
#          11:00AM = 120; 9:30PM = 750; duration = 75 minutes.
friends = [
    {"name": "Betty",     "location": "Nob Hill",          "avail_start": 270, "avail_end": 360, "duration": 15},
    {"name": "Margaret",  "location": "Russian Hill",      "avail_start": 150, "avail_end": 465, "duration": 45},
    {"name": "Mary",      "location": "Embarcadero",       "avail_start": 0,   "avail_end": 360, "duration": 90},
    {"name": "Jessica",   "location": "Union Square",      "avail_start": -15, "avail_end": 495, "duration": 15},
    {"name": "Stephanie", "location": "Golden Gate Park",  "avail_start": 270, "avail_end": 435, "duration": 45},
    {"name": "Paul",      "location": "The Castro",        "avail_start": 330, "avail_end": 525, "duration": 90},
    {"name": "Laura",     "location": "Alamo Square",      "avail_start": 525, "avail_end": 750, "duration": 105},
    {"name": "Deborah",   "location": "Fisherman's Wharf", "avail_start": 165, "avail_end": 645, "duration": 75},
    {"name": "Richard",   "location": "Sunset District",   "avail_start": 165, "avail_end": 285, "duration": 15},
    {"name": "Kenneth",   "location": "Mission District",  "avail_start": 120, "avail_end": 750, "duration": 75},
]

num_friends = len(friends)

# Define all locations mentioned.
locations = [
    "Richmond District",
    "Nob Hill",
    "Russian Hill",
    "Embarcadero",
    "Union Square",
    "Golden Gate Park",
    "The Castro",
    "Alamo Square",
    "Fisherman's Wharf",
    "Sunset District",
    "Mission District",
]

# Decision variables:
# For each friend, create:
#   x[i] -- Boolean, True if meeting with friend i is scheduled.
#   start[i] -- Integer, the start time of the meeting (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow a wide domain for start times.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, ensure:
#   (1) Meeting starts no earlier than the friend's available start.
#   (2) Meeting finishes (start + duration) by the friend's available end.
#   (3) Meeting starts no earlier than the arrival time plus travel time from Richmond District.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For every pair of meetings that are both scheduled, enforce non-overlap.
# That is, either meeting i (including its duration and travel time from i to j)
# ends before meeting j starts, or vice versa.
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

# Objective: maximize the number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the optimization problem and display the result.
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