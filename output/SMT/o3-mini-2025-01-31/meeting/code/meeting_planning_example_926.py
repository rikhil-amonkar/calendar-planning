from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# Times are measured in minutes relative to your arrival at Nob Hill at 9:00AM (time = 0).
# Please note that travel may force a later start than the raw available window.
# 
# James: North Beach, available 4:30PM-6:00PM -> [450, 540], meeting >= 90 mins.
# Deborah: Haight-Ashbury, available 6:45PM-8:15PM -> [585, 675], meeting >= 90 mins.
# Patricia: Marina District, available 12:15PM-6:00PM -> [195, 540], meeting >= 15 mins.
# Stephanie: Sunset District, available 10:15AM-7:45PM -> [75, 645], meeting >= 90 mins.
# Kenneth: Financial District, available 9:30PM-10:30PM -> [750, 810], meeting >= 15 mins.
# Michelle: Presidio, available 7:15PM-7:45PM -> [615, 645], meeting >= 30 mins.
# Rebecca: Fisherman's Wharf, available 3:45PM-8:30PM -> [405, 690], meeting >= 60 mins.
# Brian: Alamo Square, available 7:15PM-10:00PM -> [615, 780], meeting >= 45 mins.
# Ronald: Union Square, available 7:45PM-9:45PM -> [645, 765], meeting >= 30 mins.
# Jessica: Pacific Heights, available 7:30AM-3:15PM -> [ -90, 255 ], meeting >= 75 mins.
friends = [
    {"name": "James",     "location": "North Beach",      "avail_start": 450, "avail_end": 540, "duration": 90},
    {"name": "Deborah",   "location": "Haight-Ashbury",   "avail_start": 585, "avail_end": 675, "duration": 90},
    {"name": "Patricia",  "location": "Marina District",  "avail_start": 195, "avail_end": 540, "duration": 15},
    {"name": "Stephanie", "location": "Sunset District",  "avail_start": 75,  "avail_end": 645, "duration": 90},
    {"name": "Kenneth",   "location": "Financial District", "avail_start": 750, "avail_end": 810, "duration": 15},
    {"name": "Michelle",  "location": "Presidio",         "avail_start": 615, "avail_end": 645, "duration": 30},
    {"name": "Rebecca",   "location": "Fisherman's Wharf", "avail_start": 405, "avail_end": 690, "duration": 60},
    {"name": "Brian",     "location": "Alamo Square",     "avail_start": 615, "avail_end": 780, "duration": 45},
    {"name": "Ronald",    "location": "Union Square",     "avail_start": 645, "avail_end": 765, "duration": 30},
    {"name": "Jessica",   "location": "Pacific Heights",  "avail_start": -90, "avail_end": 255, "duration": 75},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Nob Hill",
    "North Beach",
    "Haight-Ashbury",
    "Marina District",
    "Sunset District",
    "Financial District",
    "Presidio",
    "Fisherman's Wharf",
    "Alamo Square",
    "Union Square",
    "Pacific Heights",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes) as provided.
travel = {
    # From Nob Hill:
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Pacific Heights"): 8,
    
    # From North Beach:
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Pacific Heights"): 8,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    
    # From Marina District:
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Pacific Heights"): 7,
    
    # From Sunset District:
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    
    # From Financial District:
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Pacific Heights"): 13,
    
    # From Presidio:
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Pacific Heights"): 11,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    
    # From Alamo Square:
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Pacific Heights"): 10,
    
    # From Union Square:
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    
    # From Pacific Heights:
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
}

# Helper function to retrieve travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use the Optimize() function to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i]: Boolean variable indicating if you schedule the meeting with friend i.
#   start[i]: Integer variable representing the meeting's start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow wide bounds for start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Nob Hill at 9:00AM (time = 0).
arrival_location = "Nob Hill"
arrival_time = 0

# For each scheduled meeting ensure:
# 1. The meeting starts no earlier than the friend’s available start.
# 2. The meeting finishes (start time + duration) by the friend’s available end.
# 3. There is enough time to travel from your arrival location (Nob Hill) to the friend’s location.
for i, friend in enumerate(friends):
    dur     = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    # Ensure meeting not scheduled before you can travel from Nob Hill.
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Pairwise non-overlap constraints:
# For any two meetings that are both scheduled, one must finish (plus travel time to the next meeting's location) before the other starts.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        # Enforce: either i is finished and you travel to j in time, or vice versa.
        no_overlap = Or(
            start[i] + dur_i + travel_i_j <= start[j],
            start[j] + dur_j + travel_j_i <= start[i]
        )
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the itinerary.
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM at Nob Hill):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        def to_time(m):
            # Convert minutes after 9:00AM (9:00 = 540 minutes after midnight) to HH:MM.
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(s_time)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")