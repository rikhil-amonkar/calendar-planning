from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
#
# All times are in minutes relative to 9:00AM (9:00AM -> 0).
# The conversion is: relative_time = (actual time in minutes from midnight) - 540.
#
# 1. Stephanie at Golden Gate Park from 12:00PM to 10:00PM; min meeting = 45 minutes.
#    12:00PM -> 720 - 540 = 180, 10:00PM -> 1320 - 540 = 780.
# 2. Richard at Fisherman's Wharf from 2:15PM to 8:15PM; min meeting = 75 minutes.
#    2:15PM -> 855 - 540 = 315, 8:15PM -> 1215 - 540 = 675.
# 3. Anthony at Haight-Ashbury from 11:45AM to 10:00PM; min meeting = 105 minutes.
#    11:45AM -> 705 - 540 = 165, 10:00PM -> 1320 - 540 = 780.
# 4. Helen at Richmond District from 9:15PM to 10:15PM; min meeting = 30 minutes.
#    9:15PM -> 1275 - 540 = 735, 10:15PM -> 1335 - 540 = 795.
# 5. Jeffrey at Mission District from 11:30AM to 4:30PM; min meeting = 15 minutes.
#    11:30AM -> 690 - 540 = 150, 4:30PM -> 990 - 540 = 450.
# 6. Sandra at Chinatown from 8:30AM to 4:30PM; min meeting = 120 minutes.
#    8:30AM -> 510 - 540 = -30, 4:30PM -> 990 - 540 = 450.
# 7. Kimberly at Russian Hill from 8:45PM to 10:00PM; min meeting = 75 minutes.
#    8:45PM -> 1305 - 540 = 765, 10:00PM -> 1320 - 540 = 780.
# 8. Joshua at North Beach from 8:30AM to 3:15PM; min meeting = 30 minutes.
#    8:30AM -> 510 - 540 = -30, 3:15PM -> 915 - 540 = 375.
# 9. Charles at Pacific Heights from 8:45PM to 10:00PM; min meeting = 75 minutes.
#    8:45PM -> 1305 - 540 = 765, 10:00PM -> 1320 - 540 = 780.
# 10. Laura at Embarcadero from 11:00AM to 7:30PM; min meeting = 60 minutes.
#     11:00AM -> 660 - 540 = 120, 7:30PM -> 1170 - 540 = 630.
friends = [
    {"name": "Stephanie", "location": "Golden Gate Park",  "avail_start": 180, "avail_end": 780, "duration": 45},
    {"name": "Richard",   "location": "Fisherman's Wharf", "avail_start": 315, "avail_end": 675, "duration": 75},
    {"name": "Anthony",   "location": "Haight-Ashbury",    "avail_start": 165, "avail_end": 780, "duration": 105},
    {"name": "Helen",     "location": "Richmond District", "avail_start": 735, "avail_end": 795, "duration": 30},
    {"name": "Jeffrey",   "location": "Mission District",  "avail_start": 150, "avail_end": 450, "duration": 15},
    {"name": "Sandra",    "location": "Chinatown",         "avail_start": -30, "avail_end": 450, "duration": 120},
    {"name": "Kimberly",  "location": "Russian Hill",      "avail_start": 765, "avail_end": 780, "duration": 75},
    {"name": "Joshua",    "location": "North Beach",       "avail_start": -30, "avail_end": 375, "duration": 30},
    {"name": "Charles",   "location": "Pacific Heights",   "avail_start": 765, "avail_end": 780, "duration": 75},
    {"name": "Laura",     "location": "Embarcadero",       "avail_start": 120, "avail_end": 630, "duration": 60},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Marina District",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Haight-Ashbury",
    "Richmond District",
    "Mission District",
    "Chinatown",
    "Russian Hill",
    "North Beach",
    "Pacific Heights",
    "Embarcadero",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes)
travel = {
    # From Marina District:
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Embarcadero"): 14,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Embarcadero"): 25,

    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Embarcadero"): 8,

    # From Haight-Ashbury:
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Embarcadero"): 20,

    # From Richmond District:
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Embarcadero"): 19,

    # From Mission District:
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Embarcadero"): 19,

    # From Chinatown:
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Embarcadero"): 7,

    # From Russian Hill:
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Embarcadero"): 8,

    # From North Beach:
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Embarcadero"): 6,

    # From Pacific Heights:
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Embarcadero"): 10,

    # From Embarcadero:
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
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
# For each friend i:
#   x[i] is a Boolean that is True if we schedule a meeting with friend i.
#   start[i] is the meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location is Marina District at 9:00AM (time=0)
starting_location = "Marina District"
arrival_time = 0

# Add constraints for each scheduled meeting:
# (a) meeting start must be at or after the friend’s available start,
# (b) meeting plus its duration must finish before available end,
# (c) enough travel time from the starting location must be allowed.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(starting_location, loc)
    
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Pairwise non-overlap constraints:
# For every pair of scheduled meetings, ensure that (meeting i + travel time to j)
# is finished before meeting j begins OR vice versa.
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
            # Convert relative minutes (after 9:00AM) to HH:MM format.
            total = 540 + minutes  # 540 minutes = 9:00AM.
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")