from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Keys are tuples (origin, destination).
travel = {
    # The Castro distances
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Sunset District"): 17,
    
    # Marina District distances
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Sunset District"): 19,
    
    # Presidio distances
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    
    # North Beach distances
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    
    # Embarcadero distances
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 4,
    ("Embarcadero", "Sunset District"): 30,
    
    # Haight-Ashbury distances
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Sunset District"): 15,
    
    # Golden Gate Park distances
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Sunset District"): 10,
    
    # Richmond District distances
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Sunset District"): 11,
    
    # Alamo Square distances
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Sunset District"): 16,
    
    # Financial District distances
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Sunset District"): 30,
    
    # Sunset District distances
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at The Castro at 9:00AM.
arrival_location = "The Castro"
arrival_time = 0  # minutes after 9:00AM

# Friend meeting data.
# All times are expressed in minutes after 9:00AM.
# (Negative times indicate periods before 9:00AM.)
# The conversion for meeting windows:
#   e.g., 7:00PM is 10 hours after 9:00AM (600 minutes)
friends = [
    {"name": "Elizabeth", "location": "Marina District",      "avail_start": 600, "avail_end": 525 + 180, "duration": 105}, # 7:00PM (600) to 8:45PM (705)
    {"name": "Joshua",    "location": "Presidio",            "avail_start": -30, "avail_end": 255,        "duration": 105}, # 8:30AM (-30) to 1:15PM (255)
    {"name": "Timothy",   "location": "North Beach",         "avail_start": 645, "avail_end": 780,        "duration": 90},  # 7:45PM (645) to 10:00PM (780)
    {"name": "David",     "location": "Embarcadero",         "avail_start": 105, "avail_end": 210,        "duration": 30},  # 10:45AM (105) to 12:30PM (210)
    {"name": "Kimberly",  "location": "Haight-Ashbury",      "avail_start": 465, "avail_end": 750,        "duration": 75},  # 4:45PM (465) to 9:30PM (750)
    {"name": "Lisa",      "location": "Golden Gate Park",    "avail_start": 510, "avail_end": 765,        "duration": 45},  # 5:30PM (510) to 9:45PM (765)
    {"name": "Ronald",    "location": "Richmond District",   "avail_start": -60, "avail_end": 30,         "duration": 90},  # 8:00AM (-60) to 9:30AM (30)
    {"name": "Stephanie", "location": "Alamo Square",        "avail_start": 390, "avail_end": 450,        "duration": 30},  # 3:30PM (390) to 4:30PM (450)
    {"name": "Helen",     "location": "Financial District",  "avail_start": 510, "avail_end": 570,        "duration": 45},  # 5:30PM (510) to 6:30PM (570)
    {"name": "Laura",     "location": "Sunset District",     "avail_start": 525, "avail_end": 750,        "duration": 90},  # 5:45PM (525) to 9:15PM (750)
]

# Note: For Elizabeth, the available window "7:00PM to 8:45PM" is encoded as 600 to 705.
# (The expression "525 + 180" equals 705.)

num_friends = len(friends)

# List of locations used.
locations = [
    "The Castro",
    "Marina District",
    "Presidio",
    "North Beach",
    "Embarcadero",
    "Haight-Ashbury",
    "Golden Gate Park",
    "Richmond District",
    "Alamo Square",
    "Financial District",
    "Sunset District",
]

# Decision variables:
# For each friend i:
#   x[i]: Boolean indicating if the meeting is scheduled.
#   start[i]: Integer representing the meeting's start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow a wide range for start times.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, add constraints:
# 1. The meeting must start no earlier than the friend’s available start time.
# 2. The meeting must finish (start + duration) by the friend’s available end time.
# 3. The meeting cannot start before you can get there from the arrival location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Add non-overlap constraints.
# For any two meetings i and j that are both scheduled, ensure that one finishes (including travel time to the next location)
# before the other starts.
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

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the scheduling problem and print the itinerary.
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