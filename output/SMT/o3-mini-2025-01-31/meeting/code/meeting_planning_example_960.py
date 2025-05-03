from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    # From The Castro
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    
    # From Nob Hill
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Haight-Ashbury"): 13,
    
    # From Pacific Heights
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    
    # From Union Square
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Haight-Ashbury"): 18,
    
    # From Mission District
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Haight-Ashbury"): 12,
    
    # From Sunset District
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    
    # From Fisherman's Wharf
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    
    # From Golden Gate Park
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    
    # From North Beach
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Haight-Ashbury"): 18,
    
    # From Richmond District
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Haight-Ashbury"): 10,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Richmond District"): 10,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at The Castro at 9:00AM.
arrival_location = "The Castro"
arrival_time = 0  # minutes after 9:00AM

# Define friend meeting information.
# All times are in minutes after 9:00AM.
# Times earlier than 9:00AM are negative.
friends = [
    {"name": "Karen",     "location": "Nob Hill",          "avail_start": -120, "avail_end": 480,  "duration": 90},  # 7:00AM to 5:00PM
    {"name": "John",      "location": "Pacific Heights",   "avail_start": 330,  "avail_end": 450,  "duration": 120}, # 2:30PM to 4:30PM
    {"name": "Joshua",    "location": "Union Square",      "avail_start": -120, "avail_end": 60,   "duration": 75},  # 7:00AM to 10:00AM
    {"name": "Emily",     "location": "Mission District",  "avail_start": 510,  "avail_end": 600,  "duration": 90},  # 5:30PM to 7:00PM
    {"name": "Stephanie", "location": "Sunset District",   "avail_start": 0,    "avail_end": 195,  "duration": 120}, # 9:00AM to 12:15PM
    {"name": "Kenneth",   "location": "Fisherman's Wharf", "avail_start": 540,  "avail_end": 705,  "duration": 15},  # 6:00PM to 8:45PM
    {"name": "Rebecca",   "location": "Golden Gate Park",  "avail_start": 405,  "avail_end": 735,  "duration": 90},  # 3:45PM to 9:15PM
    {"name": "Brian",     "location": "North Beach",       "avail_start": 30,   "avail_end": 645,  "duration": 120}, # 9:30AM to 7:45PM
    {"name": "Charles",   "location": "Richmond District", "avail_start": -45,  "avail_end": 405,  "duration": 45},  # 8:15AM to 3:45PM
    {"name": "Margaret",  "location": "Haight-Ashbury",    "avail_start": 600,  "avail_end": 645,  "duration": 45},  # 7:00PM to 7:45PM
]

num_friends = len(friends)

# List of locations used.
locations = [
    "The Castro",
    "Nob Hill",
    "Pacific Heights",
    "Union Square",
    "Mission District",
    "Sunset District",
    "Fisherman's Wharf",
    "Golden Gate Park",
    "North Beach",
    "Richmond District",
    "Haight-Ashbury",
]

# Decision variables:
# For each friend i:
#    x[i]: Boolean (whether to schedule the meeting).
#    start[i]: Integer meeting start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # A wide range is allowed.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, enforce:
# 1. Meeting must start no earlier than the friend’s available start time.
# 2. Meeting must finish (start time plus duration) by the friend’s available end time.
# 3. Meeting cannot start before you can travel from your arrival location (The Castro)
#    to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Add non-overlapping constraints.
# If meetings i and j are both scheduled, then either i finishes (plus travel time)
# before j starts, or vice versa.
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

# Objective: Maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the scheduling problem and display the optimal itinerary.
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