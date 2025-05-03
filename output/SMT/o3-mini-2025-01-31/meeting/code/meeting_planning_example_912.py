from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
#
# All times are in minutes relative to 9:00AM.
#
# 1. Kimberly at Presidio from 3:30PM to 4:00PM:
#       avail_start = 3:30PM = 390, avail_end = 420, duration 15.
# 2. Elizabeth at Alamo Square from 7:15PM to 8:15PM:
#       avail_start = 615, avail_end = 675, duration 15.
# 3. Joshua at Marina District from 10:30AM to 2:15PM:
#       avail_start = 90, avail_end = 315, duration 45.
# 4. Sandra at Financial District from 7:30PM to 8:15PM:
#       avail_start = 630, avail_end = 675, duration 45.
# 5. Kenneth at Nob Hill from 12:45PM to 9:45PM:
#       avail_start = 225, avail_end = 705, duration 30.
# 6. Betty at Sunset District from 2:00PM to 7:00PM:
#       avail_start = 300, avail_end = 600, duration 60.
# 7. Deborah at Chinatown from 5:15PM to 8:30PM:
#       avail_start = 495, avail_end = 690, duration 15.
# 8. Barbara at Russian Hill from 5:30PM to 9:15PM:
#       avail_start = 510, avail_end = 735, duration 120.
# 9. Steven at North Beach from 5:45PM to 8:45PM:
#       avail_start = 525, avail_end = 705, duration 90.
# 10. Daniel at Haight-Ashbury from 6:30PM to 6:45PM:
#       avail_start = 570, avail_end = 585, duration 15.
friends = [
    {"name": "Kimberly",  "location": "Presidio",           "avail_start": 390, "avail_end": 420, "duration": 15},
    {"name": "Elizabeth",  "location": "Alamo Square",       "avail_start": 615, "avail_end": 675, "duration": 15},
    {"name": "Joshua",     "location": "Marina District",    "avail_start": 90,  "avail_end": 315, "duration": 45},
    {"name": "Sandra",     "location": "Financial District", "avail_start": 630, "avail_end": 675, "duration": 45},
    {"name": "Kenneth",    "location": "Nob Hill",           "avail_start": 225, "avail_end": 705, "duration": 30},
    {"name": "Betty",      "location": "Sunset District",    "avail_start": 300, "avail_end": 600, "duration": 60},
    {"name": "Deborah",    "location": "Chinatown",          "avail_start": 495, "avail_end": 690, "duration": 15},
    {"name": "Barbara",    "location": "Russian Hill",       "avail_start": 510, "avail_end": 735, "duration": 120},
    {"name": "Steven",     "location": "North Beach",        "avail_start": 525, "avail_end": 705, "duration": 90},
    {"name": "Daniel",     "location": "Haight-Ashbury",     "avail_start": 570, "avail_end": 585, "duration": 15},
]

# ---------------------------------------------------------------------
# List of locations (include the starting point Union Square).
locations = [
    "Union Square",
    "Presidio",
    "Alamo Square",
    "Marina District",
    "Financial District",
    "Nob Hill",
    "Sunset District",
    "Chinatown",
    "Russian Hill",
    "North Beach",
    "Haight-Ashbury",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# The keys are tuples (origin, destination).
travel = {
    # From Union Square:
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Haight-Ashbury"): 18,
    
    # From Presidio:
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Haight-Ashbury"): 15,
    
    # From Alamo Square:
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Haight-Ashbury"): 5,
    
    # From Marina District:
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Haight-Ashbury"): 16,
    
    # From Financial District:
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Haight-Ashbury"): 19,
    
    # From Nob Hill:
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    
    # From Sunset District:
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Haight-Ashbury"): 15,
    
    # From Chinatown:
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Haight-Ashbury"): 19,
    
    # From Russian Hill:
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Haight-Ashbury"): 17,
    
    # From North Beach:
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Haight-Ashbury"): 18,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   For each friend i:
#      x[i] is a Boolean that is True if we schedule a meeting with friend i.
#      start[i] is the meeting start time (in minutes relative to 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting at Union Square at 9:00AM (time 0)
starting_location = "Union Square"
arrival_time = 0

# For each friend scheduled, ensure:
# (a) Meeting start is not before the friend’s available start,
# (b) Meeting plus duration finishes by the available end,
# (c) And that you have enough time to travel from the starting location.
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
# For any two scheduled meetings, ensure that one meeting (plus required travel time) is finished
# before the other starts.
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
            total = 9*60 + minutes
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")