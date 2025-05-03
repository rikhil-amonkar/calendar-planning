from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    # From Bayview
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Pacific Heights"): 23,
    
    # From Marina District
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7,
    
    # From Union Square
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Pacific Heights"): 15,
    
    # From Alamo Square
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Pacific Heights"): 10,
    
    # From Mission District
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Pacific Heights"): 16,
    
    # From Golden Gate Park
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Pacific Heights"): 16,
    
    # From Chinatown
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Pacific Heights"): 10,
    
    # From Sunset District
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Pacific Heights"): 21,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    
    # From Richmond District
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Pacific Heights"): 10,
    
    # From Pacific Heights
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Richmond District"): 12,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at Bayview at 9:00AM.
arrival_location = "Bayview"
arrival_time = 0  # minutes after 9:00AM

# Define the friend meeting information.
# Times are given as minutes after 9:00AM.
friends = [
    {"name": "Deborah",  "location": "Marina District",   "avail_start": 675, "avail_end": 765, "duration": 75},  # 8:15PM (675) to 9:45PM (765)
    {"name": "Linda",    "location": "Union Square",       "avail_start": 645, "avail_end": 780, "duration": 75},  # 7:45PM (645) to 10:00PM (780)
    {"name": "Carol",    "location": "Alamo Square",       "avail_start": 360, "avail_end": 690, "duration": 120}, # 3:00PM (360) to 6:30PM (690)
    {"name": "Rebecca",  "location": "Mission District",   "avail_start": 480, "avail_end": 645, "duration": 15},  # 5:00PM (480) to 7:45PM (645)
    {"name": "Michelle", "location": "Golden Gate Park",   "avail_start": 135, "avail_end": 870, "duration": 75},  # 11:15AM (135) to 8:30PM (870)
    {"name": "Melissa",  "location": "Chinatown",          "avail_start": 195, "avail_end": 270, "duration": 30},  # 12:15PM (195) to 1:30PM (270)
    {"name": "Jeffrey",  "location": "Sunset District",    "avail_start": 375, "avail_end": 720, "duration": 120}, # 4:15PM (375) to 9:00PM (720)
    {"name": "Mark",     "location": "Haight-Ashbury",     "avail_start": -120,"avail_end": 165, "duration": 75},  # 7:00AM (-120) to 11:45AM (165)
    {"name": "Margaret", "location": "Richmond District",  "avail_start": 150, "avail_end": 375, "duration": 15},  # 11:30AM (150) to 3:15PM (375)
    {"name": "Charles",  "location": "Pacific Heights",    "avail_start": 285, "avail_end": 735, "duration": 75},  # 1:45PM (285) to 9:15PM (735)
]

num_friends = len(friends)

# List of the involved locations.
locations = [
    "Bayview",
    "Marina District",
    "Union Square",
    "Alamo Square",
    "Mission District",
    "Golden Gate Park",
    "Chinatown",
    "Sunset District",
    "Haight-Ashbury",
    "Richmond District",
    "Pacific Heights",
]

# Decision variables: for each friend i, we have:
#  x[i]: Boolean whether the meeting is scheduled.
#  start[i]: Integer start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow a wide range for start times.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each friend scheduled, enforce:
# 1. The start time must be at or after the friend's available start.
# 2. The meeting must end no later than the friend's available end.
# 3. The meeting cannot start before you can travel from the arrival location (Bayview)
#    to the friend's location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end   = friend["avail_end"]
    loc         = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Add non-overlapping constraints.
# If meetings i and j are both scheduled, then one must finish (including travel time
# from its location to the next meeting's location) before the other starts.
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

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the scheduling problem and output the itinerary.
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