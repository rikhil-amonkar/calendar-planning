from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are measured in minutes after 9:00AM when you arrive at Bayview (time = 0).
# The conversion for clock times is as follows:
#
# Richard: at Fisherman's Wharf from 12:00PM to 2:00PM.
#   12:00PM is 180 minutes after 9:00AM; 2:00PM is 300 minutes.
#   Minimum duration: 120 minutes.
#
# Brian: at Chinatown from 4:00PM to 6:30PM.
#   4:00PM is 420 minutes; 6:30PM is 570 minutes.
#   Minimum duration: 120 minutes.
#
# Sarah: at Alamo Square from 3:30PM to 5:30PM.
#   3:30PM is 390 minutes; 5:30PM is 510 minutes.
#   Minimum duration: 60 minutes.
#
# Paul: at Presidio from 12:30PM to 4:30PM.
#   12:30PM is 210 minutes; 4:30PM is 450 minutes.
#   Minimum duration: 90 minutes.
#
# Joseph: at Pacific Heights from 4:00PM to 8:15PM.
#   4:00PM is 420 minutes; 8:15PM is 675 minutes.
#   Minimum duration: 120 minutes.
#
# Mary: at Embarcadero from 9:15PM to 10:00PM.
#   9:15PM is 735 minutes; 10:00PM is 780 minutes.
#   Minimum duration: 30 minutes.
#
# Barbara: at Union Square from 9:00PM to 10:00PM.
#   9:00PM is 720 minutes; 10:00PM is 780 minutes.
#   Minimum duration: 30 minutes.
#
# Karen: at The Castro from 11:30AM to 9:45PM.
#   11:30AM is 150 minutes; 9:45PM is 765 minutes.
#   Minimum duration: 45 minutes.
#
# Kenneth: at Haight-Ashbury from 6:30PM to 8:15PM.
#   6:30PM is 570 minutes; 8:15PM is 675 minutes.
#   Minimum duration: 60 minutes.
#
# Deborah: at North Beach from 3:45PM to 7:00PM.
#   3:45PM is 405 minutes; 7:00PM is 600 minutes.
#   Minimum duration: 75 minutes.
friends = [
    {"name": "Richard",  "location": "Fisherman's Wharf", "avail_start": 180, "avail_end": 300, "duration": 120},
    {"name": "Brian",    "location": "Chinatown",         "avail_start": 420, "avail_end": 570, "duration": 120},
    {"name": "Sarah",    "location": "Alamo Square",      "avail_start": 390, "avail_end": 510, "duration": 60},
    {"name": "Paul",     "location": "Presidio",          "avail_start": 210, "avail_end": 450, "duration": 90},
    {"name": "Joseph",   "location": "Pacific Heights",   "avail_start": 420, "avail_end": 675, "duration": 120},
    {"name": "Mary",     "location": "Embarcadero",       "avail_start": 735, "avail_end": 780, "duration": 30},
    {"name": "Barbara",  "location": "Union Square",      "avail_start": 720, "avail_end": 780, "duration": 30},
    {"name": "Karen",    "location": "The Castro",        "avail_start": 150, "avail_end": 765, "duration": 45},
    {"name": "Kenneth",  "location": "Haight-Ashbury",    "avail_start": 570, "avail_end": 675, "duration": 60},
    {"name": "Deborah",  "location": "North Beach",       "avail_start": 405, "avail_end": 600, "duration": 75},
]

# -----------------------------------------------------------------------------
# List of locations.
# Your arrival location is Bayview.
locations = [
    "Bayview",            # Arrival location at 9:00AM.
    "Fisherman's Wharf",
    "Chinatown",
    "Alamo Square",
    "Presidio",
    "Pacific Heights",
    "Embarcadero",
    "Union Square",
    "The Castro",
    "Haight-Ashbury",
    "North Beach",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Bayview:
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "North Beach"): 22,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "North Beach"): 6,
    
    # From Chinatown:
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "North Beach"): 3,
    
    # From Alamo Square:
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "North Beach"): 15,
    
    # From Presidio:
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "North Beach"): 18,
    
    # From Pacific Heights:
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "North Beach"): 9,
    
    # From Embarcadero:
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "North Beach"): 5,
    
    # From Union Square:
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "North Beach"): 10,
    
    # From The Castro:
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "North Beach"): 20,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    
    # From North Beach:
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Haight-Ashbury"): 18,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i]: Boolean indicator whether meeting friend i is scheduled.
# start[i]: meeting start time (minutes after 9:00AM at Bayview).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow start times to vary in a wide range.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Bayview at 9:00AM (time=0).
arrival_location = "Bayview"
arrival_time = 0

# For each friend scheduled, enforce that:
# - Their meeting starts no earlier than their available start.
# - Their meeting finishes (start + duration) by their available end.
# - You account for the travel time from the arrival location (Bayview) to the meeting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Pairwise non-overlap constraints.
# For any two scheduled meetings, ensure that either meeting i (plus its duration and travel from its location to j)
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
    # Sort scheduled meetings in order of start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Bayview):")
    
    def format_time(m):
        # Convert minutes after 9:00AM (9:00AM = 540 min after midnight)
        total = 540 + m
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")