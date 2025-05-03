from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# All times are measured in minutes after 9:00AM at Embarcadero (time = 0).
# Times have been converted as follows:
# Sarah: at Mission District, from 7:45PM to 9:45PM -> [645, 765], minimum duration 120 minutes.
# Stephanie: at Presidio, from 1:15PM to 7:00PM -> [255, 600], minimum duration 90 minutes.
# Ashley: at Financial District, from 7:00PM to 10:00PM -> [600, 780], minimum duration 75 minutes.
# Linda: at Chinatown, from 9:30AM to 9:00PM -> [30, 720], minimum duration 15 minutes.
# Helen: at Fisherman's Wharf, from 9:45AM to 6:00PM -> [45, 540], minimum duration 60 minutes.
# Carol: at Bayview, from 11:30AM to 5:45PM -> [150, 525], minimum duration 60 minutes.
# Sandra: at The Castro, from 7:30PM to 9:45PM -> [630, 765], minimum duration 105 minutes.
# Melissa: at Richmond District, from 12:00PM to 4:45PM -> [180, 465], minimum duration 120 minutes.
# James: at Pacific Heights, from 9:30PM to 10:30PM -> [750, 810], minimum duration 60 minutes.
# Brian: at Nob Hill, from 7:00PM to 8:30PM -> [600, 690], minimum duration 30 minutes.
friends = [
    {"name": "Sarah",     "location": "Mission District",   "avail_start": 645, "avail_end": 765, "duration": 120},
    {"name": "Stephanie", "location": "Presidio",           "avail_start": 255, "avail_end": 600, "duration": 90},
    {"name": "Ashley",    "location": "Financial District", "avail_start": 600, "avail_end": 780, "duration": 75},
    {"name": "Linda",     "location": "Chinatown",          "avail_start": 30,  "avail_end": 720, "duration": 15},
    {"name": "Helen",     "location": "Fisherman's Wharf",  "avail_start": 45,  "avail_end": 540, "duration": 60},
    {"name": "Carol",     "location": "Bayview",            "avail_start": 150, "avail_end": 525, "duration": 60},
    {"name": "Sandra",    "location": "The Castro",         "avail_start": 630, "avail_end": 765, "duration": 105},
    {"name": "Melissa",   "location": "Richmond District",  "avail_start": 180, "avail_end": 465, "duration": 120},
    {"name": "James",     "location": "Pacific Heights",    "avail_start": 750, "avail_end": 810, "duration": 60},
    {"name": "Brian",     "location": "Nob Hill",           "avail_start": 600, "avail_end": 690, "duration": 30},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Embarcadero",
    "Mission District",
    "Presidio",
    "Financial District",
    "Chinatown",
    "Fisherman's Wharf",
    "Bayview",
    "The Castro",
    "Richmond District",
    "Pacific Heights",
    "Nob Hill",
]

# -----------------------------------------------------------------------------
# Travel distances between locations (in minutes).
# Each tuple (origin, destination) maps to the travel time.
travel = {
    # From Embarcadero:
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    
    # From Mission District:
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Nob Hill"): 12,
    
    # From Presidio:
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Nob Hill"): 18,
    
    # From Financial District:
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    
    # From Chinatown:
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Nob Hill"): 9,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    
    # From Bayview:
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
    
    # From The Castro:
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    
    # From Richmond District:
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Nob Hill"): 17,
    
    # From Pacific Heights:
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    
    # From Nob Hill:
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Pacific Heights"): 8,
}

# Helper function to obtain travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 Model and Optimization.
# -----------------------------------------------------------------------------
# Create an Optimize instance to maximize the total number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i]: Boolean variable that indicates whether to schedule a meeting with friend i.
#   start[i]: Integer variable for the meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow start times to be in a broad range.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Embarcadero at 9:00AM (time = 0).
arrival_location = "Embarcadero"
arrival_time = 0

# For each scheduled meeting, ensure that:
#   1. The meeting starts no earlier than the friend's available start time.
#   2. The meeting (start time + duration) finishes before or at the available end time.
#   3. You can only begin the meeting after arriving at that location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_time = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_time))

# Add pairwise non-overlap constraints.
# If two meetings are scheduled, then after meeting i (plus travel time from friend i's location to j's location)
# the meeting j must not start before that time, or vice versa.
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

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve and print the optimal itinerary.
# -----------------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Embarcadero):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        def to_time(m):
            # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) to HH:MM.
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(s_time)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")