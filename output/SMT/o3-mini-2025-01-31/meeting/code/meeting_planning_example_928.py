from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# All times are relative to your arrival at Union Square at 9:00AM (time = 0).
# When converting clock times, note:
#   e.g., 11:00AM is 60* (11-9) = 120 minutes and 2:30PM is 330 minutes.
#
# Jason: at Marina District, available 11:00AM to 2:30PM, meeting >= 105 minutes.
# Michelle: at North Beach, available 8:00PM to 9:15PM, meeting >= 60 minutes.
# Carol: at Richmond District, available 8:30PM to 9:30PM, meeting >= 15 minutes.
# Sandra: at Haight-Ashbury, available 8:00PM to 9:15PM, meeting >= 15 minutes.
# Paul: at Embarcadero, available 4:30PM to 9:30PM, meeting >= 75 minutes.
# Jeffrey: at Presidio, available 11:30AM to 10:00PM, meeting >= 105 minutes.
# Patricia: at Chinatown, available 9:30AM to 12:45PM, meeting >= 120 minutes.
# Barbara: at Mission District, available 11:00AM to 1:15PM, meeting >= 90 minutes.
# Daniel: at Sunset District, available 8:15AM to 3:15PM, meeting >= 30 minutes.
# Sarah: at Golden Gate Park, available 8:00PM to 9:30PM, meeting >= 45 minutes.
friends = [
    {"name": "Jason",     "location": "Marina District",  "avail_start": 120, "avail_end": 330, "duration": 105},
    {"name": "Michelle",  "location": "North Beach",       "avail_start": 660, "avail_end": 735, "duration": 60},
    {"name": "Carol",     "location": "Richmond District", "avail_start": 690, "avail_end": 750, "duration": 15},
    {"name": "Sandra",    "location": "Haight-Ashbury",    "avail_start": 660, "avail_end": 735, "duration": 15},
    {"name": "Paul",      "location": "Embarcadero",       "avail_start": 450, "avail_end": 750, "duration": 75},
    {"name": "Jeffrey",   "location": "Presidio",          "avail_start": 150, "avail_end": 780, "duration": 105},
    {"name": "Patricia",  "location": "Chinatown",         "avail_start": 30,  "avail_end": 225, "duration": 120},
    {"name": "Barbara",   "location": "Mission District",  "avail_start": 120, "avail_end": 255, "duration": 90},
    {"name": "Daniel",    "location": "Sunset District",   "avail_start": -45, "avail_end": 255, "duration": 30},
    {"name": "Sarah",     "location": "Golden Gate Park",  "avail_start": 660, "avail_end": 750, "duration": 45},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Union Square",
    "Marina District",
    "North Beach",
    "Richmond District",
    "Haight-Ashbury",
    "Embarcadero",
    "Presidio",
    "Chinatown",
    "Mission District",
    "Sunset District",
    "Golden Gate Park",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
travel = {
    # From Union Square:
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,
    
    # From Marina District:
    ("Marina District", "Union Square"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,
    
    # From North Beach:
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Golden Gate Park"): 22,
    
    # From Richmond District:
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Golden Gate Park"): 9,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    
    # From Embarcadero:
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Golden Gate Park"): 25,
    
    # From Presidio:
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Golden Gate Park"): 12,
    
    # From Chinatown:
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Golden Gate Park"): 23,
    
    # From Mission District:
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,
    
    # From Sunset District:
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Golden Gate Park"): 11,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Sunset District"): 10,
}

# Helper function to get travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use the Optimize() solver to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i] is a Boolean variable indicating whether to schedule a meeting with friend i.
# start[i] is the integer start time of the meeting (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set wide bounds for possible meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Union Square at 9:00AM (time = 0).
arrival_location = "Union Square"
arrival_time = 0

# For each scheduled meeting, enforce:
# 1. The meeting start time is not before the friend’s available start.
# 2. The meeting (plus its duration) finishes by the friend’s available end.
# 3. The meeting does not start until you have time to travel from Union Square.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Add pairwise non-overlap constraints.
# For any two meetings scheduled, ensure that after accounting for meeting durations and travel time between locations,
# one meeting finishes before the other starts.
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

# Objective: maximize the total number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the optimal itinerary.
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Union Square):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        def to_time(m):
            # Convert m minutes after 9:00AM (9:00AM = 540 minutes after midnight) to HH:MM.
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(s_time)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")