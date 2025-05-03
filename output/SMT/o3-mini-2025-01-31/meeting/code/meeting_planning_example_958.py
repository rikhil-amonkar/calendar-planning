from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Note: Distances are not necessarily symmetric.
travel = {
    # From Golden Gate Park
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Pacific Heights"): 16,
    
    # From Financial District
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Pacific Heights"): 13,
    
    # From Union Square
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Mission District"): 15,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Pacific Heights"): 15,
    
    # From Nob Hill
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Pacific Heights"): 8,
    
    # From Mission District
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Pacific Heights"): 16,
    
    # From Alamo Square
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Pacific Heights"): 10,
    
    # From Chinatown
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Pacific Heights"): 10,
    
    # From Embarcadero
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Pacific Heights"): 11,
    
    # From Bayview
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 27,
    ("Bayview", "Pacific Heights"): 23,
    
    # From Richmond District
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Pacific Heights"): 10,
    
    # From Pacific Heights
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Richmond District"): 12,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at Golden Gate Park at 9:00AM.
arrival_location = "Golden Gate Park"
arrival_time = 0  # minutes after 9:00AM

# Friend meeting information.
# All times are in minutes after 9:00AM. Note: Times earlier than 9:00AM are negative.
# For example, 8:45AM is -15 and 9:45AM is 45.
friends = [
    {"name": "Helen",   "location": "Financial District", "avail_start": -15, "avail_end": 525,  "duration": 60},
    {"name": "Sarah",   "location": "Union Square",       "avail_start": 45,   "avail_end": 360,  "duration": 45},
    {"name": "Andrew",  "location": "Nob Hill",           "avail_start": 270,  "avail_end": 645,  "duration": 30},
    {"name": "Rebecca", "location": "Mission District",   "avail_start": 555,  "avail_end": 720,  "duration": 90},
    {"name": "Kimberly","location": "Alamo Square",       "avail_start": 270,  "avail_end": 690,  "duration": 45},
    {"name": "Mark",    "location": "Chinatown",          "avail_start": 105,  "avail_end": 255,  "duration": 15},
    {"name": "Timothy", "location": "Embarcadero",        "avail_start": -120, "avail_end": 330,  "duration": 75},
    {"name": "James",   "location": "Bayview",            "avail_start": 540,  "avail_end": 705,  "duration": 120},
    {"name": "Jessica", "location": "Richmond District",  "avail_start": 360,  "avail_end": 585,  "duration": 15},
    {"name": "William", "location": "Pacific Heights",    "avail_start": 585,  "avail_end": 645,  "duration": 60},
]

num_friends = len(friends)

# List of all locations involved.
locations = [
    "Golden Gate Park",
    "Financial District",
    "Union Square",
    "Nob Hill",
    "Mission District",
    "Alamo Square",
    "Chinatown",
    "Embarcadero",
    "Bayview",
    "Richmond District",
    "Pacific Heights",
]

# Decision variables:
# For each friend i, define:
#   x[i]: Boolean, whether the meeting is scheduled.
#   start[i]: Integer, meeting start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow start times in a wide interval.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each meeting that is scheduled, enforce:
# 1. The meeting must not start before the friend's available start.
# 2. The meeting must finish (start + duration) by the friend's available end.
# 3. The meeting's start time must be no earlier than the time it takes to travel
#    from the arrival location (Golden Gate Park) to that friend's location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end   = friend["avail_end"]
    loc         = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Impose non-overlapping constraints between every pair of scheduled meetings.
# If both meetings i and j are scheduled, then either i finishes (including travel time
# from i’s location to j’s location) before j starts, or j likewise finishes before i starts.
for i in range(num_friends):
    for j in range(i + 1, num_friends):
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

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the scheduling problem and print the optimal itinerary.
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