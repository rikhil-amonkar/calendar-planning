from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are measured as minutes after 9:00AM at Chinatown (time = 0).
#
# James: at Richmond District from 1:45PM to 3:00PM.
#   1:45PM is 4h45 after 9:00AM -> 285 minutes;
#   3:00PM is 6h after 9:00AM -> 360 minutes.
#   Minimum duration: 30 minutes.
#
# Emily: at Alamo Square from 5:00PM to 7:00PM.
#   5:00PM -> 8h after 9:00AM -> 480 minutes;
#   7:00PM -> 10h after 9:00AM -> 600 minutes.
#   Minimum duration: 15 minutes.
#
# Kevin: at Embarcadero from 9:15PM to 10:15PM.
#   9:15PM -> 12h15 after 9:00AM -> 735 minutes;
#   10:15PM -> 13h15 after 9:00AM -> 795 minutes.
#   Minimum duration: 30 minutes.
#
# Sarah: at Bayview from 10:00AM to 5:15PM.
#   10:00AM -> 60 minutes after 9:00AM;
#   5:15PM -> 8h15 after 9:00AM -> 495 minutes.
#   Minimum duration: 60 minutes.
#
# Andrew: at Golden Gate Park from 9:00PM to 9:15PM.
#   9:00PM -> 12h after 9:00AM -> 720 minutes;
#   9:15PM -> 735 minutes.
#   Minimum duration: 15 minutes.
#
# Jeffrey: at The Castro from 7:00AM to 6:00PM.
#   7:00AM -> -120 minutes (before 9:00AM);
#   6:00PM -> 9h after 9:00AM -> 540 minutes.
#   Minimum duration: 75 minutes.
#
# Michelle: at Mission District from 11:30AM to 6:45PM.
#   11:30AM -> 2h30 after 9:00AM -> 150 minutes;
#   6:45PM -> 9h45 after 9:00AM -> 585 minutes.
#   Minimum duration: 60 minutes.
#
# Betty: at Fisherman's Wharf from 7:15PM to 9:15PM.
#   7:15PM -> 10h15 after 9:00AM -> 615 minutes;
#   9:15PM -> 12h15 after 9:00AM -> 735 minutes.
#   Minimum duration: 45 minutes.
#
# Daniel: at Haight-Ashbury from 7:45PM to 10:00PM.
#   7:45PM -> 10h45 after 9:00AM -> 645 minutes;
#   10:00PM -> 13h after 9:00AM -> 780 minutes.
#   Minimum duration: 120 minutes.
#
# Mark: at Marina District from 2:30PM to 8:30PM.
#   2:30PM -> 5h30 after 9:00AM -> 330 minutes;
#   8:30PM -> 11h30 after 9:00AM -> 690 minutes.
#   Minimum duration: 90 minutes.
friends = [
    {"name": "James",    "location": "Richmond District",  "avail_start": 285, "avail_end": 360, "duration": 30},
    {"name": "Emily",    "location": "Alamo Square",       "avail_start": 480, "avail_end": 600, "duration": 15},
    {"name": "Kevin",    "location": "Embarcadero",        "avail_start": 735, "avail_end": 795, "duration": 30},
    {"name": "Sarah",    "location": "Bayview",            "avail_start": 60,  "avail_end": 495, "duration": 60},
    {"name": "Andrew",   "location": "Golden Gate Park",   "avail_start": 720, "avail_end": 735, "duration": 15},
    {"name": "Jeffrey",  "location": "The Castro",         "avail_start": -120,"avail_end": 540, "duration": 75},
    {"name": "Michelle", "location": "Mission District",   "avail_start": 150, "avail_end": 585, "duration": 60},
    {"name": "Betty",    "location": "Fisherman's Wharf",  "avail_start": 615, "avail_end": 735, "duration": 45},
    {"name": "Daniel",   "location": "Haight-Ashbury",     "avail_start": 645, "avail_end": 780, "duration": 120},
    {"name": "Mark",     "location": "Marina District",    "avail_start": 330, "avail_end": 690, "duration": 90},
]

# -----------------------------------------------------------------------------
# List of locations.
# Your arrival location is Chinatown.
locations = [
    "Chinatown",         # Arrival location at 9:00AM.
    "Richmond District",
    "Alamo Square",
    "Embarcadero",
    "Bayview",
    "Golden Gate Park",
    "The Castro",
    "Mission District",
    "Fisherman's Wharf",
    "Haight-Ashbury",
    "Marina District",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Chinatown:
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Marina District"): 12,

    # From Richmond District:
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Marina District"): 9,

    # From Alamo Square:
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Marina District"): 15,

    # From Embarcadero:
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Marina District"): 12,

    # From Bayview:
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Marina District"): 27,

    # From Golden Gate Park:
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Marina District"): 16,

    # From The Castro:
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Marina District"): 21,

    # From Mission District:
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Marina District"): 19,

    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Marina District"): 9,

    # From Haight-Ashbury:
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,

    # From Marina District:
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i] is a Boolean indicating whether meeting friend i is scheduled.
# start[i] is an integer representing the meeting start time (in minutes after 9:00AM at Chinatown).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
# Give start times a wide range.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Chinatown at 9:00AM (time=0).
arrival_location = "Chinatown"
arrival_time = 0

# For each friend scheduled, require:
# - The meeting starts no earlier than their available start.
# - It finishes (start + duration) by their available end.
# - The start time is no earlier than the arrival time plus travel time from Chinatown.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Pairwise non-overlap constraints:
# For any two scheduled meetings, ensure that either meeting i (plus its duration and travel time from its location to j)
# finishes before meeting j starts, or vice versa.
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

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    # Sort the meetings by start time:
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Chinatown):")
    
    def format_time(m):
        # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) into HH:MM.
        total = 540 + m
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")