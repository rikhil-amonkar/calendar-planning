from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes). They are given as ordered pairs.
travel = {
    # From The Castro:
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    
    # From Alamo Square:
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    
    # From Richmond District:
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    
    # From Financial District:
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    
    # From Union Square:
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    
    # From Marina District:
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    
    # From Mission District:
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    
    # From Pacific Heights:
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Pacific Heights"): 16,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimization model.
opt = Optimize()

# You arrive at The Castro at 9:00AM.
arrival_location = "The Castro"
arrival_time = 0  # minutes after 9:00AM

# Friend meeting parameters.
# All times are measured in minutes after 9:00AM. For example, 3:15PM is 375 minutes after 9:00AM.
friends = [
    {"name": "William",   "location": "Alamo Square",    "avail_start": 375, "avail_end": 495, "duration": 60},
    {"name": "Joshua",    "location": "Richmond District", "avail_start": -120, "avail_end": 660, "duration": 15},
    {"name": "Joseph",    "location": "Financial District","avail_start": 135, "avail_end": 270, "duration": 15},
    {"name": "David",     "location": "Union Square",      "avail_start": 465, "avail_end": 615, "duration": 45},
    {"name": "Brian",     "location": "Fisherman's Wharf", "avail_start": 285, "avail_end": 705, "duration": 105},
    {"name": "Karen",     "location": "Marina District",   "avail_start": 150, "avail_end": 570, "duration": 15},
    {"name": "Anthony",   "location": "Haight-Ashbury",    "avail_start": -105, "avail_end": 90, "duration": 30},
    {"name": "Matthew",   "location": "Mission District",  "avail_start": 495, "avail_end": 615, "duration": 120},
    {"name": "Helen",     "location": "Pacific Heights",   "avail_start": -60, "avail_end": 180, "duration": 75},
    {"name": "Jeffrey",   "location": "Golden Gate Park",  "avail_start": 600, "avail_end": 750, "duration": 60},
]

num_friends = len(friends)

# List of all locations involved.
locations = [
    "The Castro",
    "Alamo Square",
    "Richmond District",
    "Financial District",
    "Union Square",
    "Fisherman's Wharf",
    "Marina District",
    "Haight-Ashbury",
    "Mission District",
    "Pacific Heights",
    "Golden Gate Park",
]

# Decision variables:
# For each friend i we create:
#   x[i]: a Boolean variable indicating whether meeting friend i is scheduled.
#   start[i]: an integer variable representing the meeting’s start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow start times in a wide interval.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each friend meeting that is scheduled, enforce:
# 1. The meeting must not start before the friend’s available start.
# 2. The meeting must finish (start + duration) by the friend’s available end.
# 3. The meeting cannot start before you can get from your arrival location to the meeting’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For every pair of scheduled meetings, enforce non-overlap.
# That is, if meetings i and j are both scheduled then either meeting i (plus its duration and the travel time from its location to j's)
# finishes before meeting j starts, or vice-versa.
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
# Solve the scheduling problem and print the optimal schedule.
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