from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are measured in minutes relative to 9:00AM at Pacific Heights (time = 0).
# Convert the clock times as follows:
#
# Rebecca: at Chinatown from 8:15PM to 8:30PM.
#    8:15PM is 11h15m after 9:00AM => 675 minutes.
#    8:30PM is 11h30m after 9:00AM => 690 minutes.
#    Duration = 15 minutes.
#
# Kenneth: at Richmond District from 4:30PM to 5:45PM.
#    4:30PM is 7h30m after 9:00AM => 450 minutes.
#    5:45PM is 8h45m after 9:00AM => 525 minutes.
#    Duration = 75 minutes.
#
# Carol: at Union Square from 2:45PM to 9:00PM.
#    2:45PM is 5h45m after 9:00AM => 345 minutes.
#    9:00PM is 12:00h after 9:00AM => 720 minutes.
#    Duration = 45 minutes.
#
# Karen: at Bayview from 3:45PM to 9:00PM.
#    3:45PM is 6h45m after 9:00AM => 405 minutes.
#    9:00PM is 720 minutes.
#    Duration = 30 minutes.
#
# Helen: at Haight-Ashbury from 8:00PM to 9:45PM.
#    8:00PM is 11h00m after 9:00AM => 660 minutes.
#    9:45PM is 12h45m after 9:00AM => 765 minutes.
#    Duration = 15 minutes.
#
# Robert: at Sunset District from 5:00PM to 9:00PM.
#    5:00PM is 8:00m after 9:00AM => 480 minutes.
#    9:00PM is 720 minutes.
#    Duration = 120 minutes.
#
# Richard: at Nob Hill from 8:00PM to 8:30PM.
#    8:00PM is 11h00m after 9:00AM => 660 minutes.
#    8:30PM is 11h30m after 9:00AM => 690 minutes.
#    Duration = 30 minutes.
#
# Melissa: at Embarcadero from 2:45PM to 7:00PM.
#    2:45PM is 5h45m after 9:00AM => 345 minutes.
#    7:00PM is 10:00h after 9:00AM => 600 minutes.
#    Duration = 75 minutes.
#
# Brian: at Presidio from 9:00AM to 6:45PM.
#    9:00AM is time 0; 6:45PM is 9h45m after 9:00AM => 585 minutes.
#    Duration = 75 minutes.
#
# Margaret: at Mission District from 1:30PM to 7:00PM.
#    1:30PM is 4h30m after 9:00AM => 270 minutes.
#    7:00PM is 600 minutes.
#    Duration = 105 minutes.
friends = [
    {"name": "Rebecca",  "location": "Chinatown",         "avail_start": 675, "avail_end": 690, "duration": 15},
    {"name": "Kenneth",  "location": "Richmond District",  "avail_start": 450, "avail_end": 525, "duration": 75},
    {"name": "Carol",    "location": "Union Square",       "avail_start": 345, "avail_end": 720, "duration": 45},
    {"name": "Karen",    "location": "Bayview",            "avail_start": 405, "avail_end": 720, "duration": 30},
    {"name": "Helen",    "location": "Haight-Ashbury",     "avail_start": 660, "avail_end": 765, "duration": 15},
    {"name": "Robert",   "location": "Sunset District",    "avail_start": 480, "avail_end": 720, "duration": 120},
    {"name": "Richard",  "location": "Nob Hill",           "avail_start": 660, "avail_end": 690, "duration": 30},
    {"name": "Melissa",  "location": "Embarcadero",        "avail_start": 345, "avail_end": 600, "duration": 75},
    {"name": "Brian",    "location": "Presidio",           "avail_start": 0,   "avail_end": 585, "duration": 75},
    {"name": "Margaret", "location": "Mission District",   "avail_start": 270, "avail_end": 600, "duration": 105},
]

# -----------------------------------------------------------------------------
# List of locations.
# Note: Your arrival location is Pacific Heights.
locations = [
    "Pacific Heights",  # Arrival location at 9:00AM.
    "Chinatown",
    "Richmond District",
    "Union Square",
    "Bayview",
    "Haight-Ashbury",
    "Sunset District",
    "Nob Hill",
    "Embarcadero",
    "Presidio",
    "Mission District",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Pacific Heights:
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Mission District"): 15,
    
    # From Chinatown:
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Mission District"): 17,
    
    # From Richmond District:
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Mission District"): 20,
    
    # From Union Square:
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Mission District"): 14,
    
    # From Bayview:
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Mission District"): 13,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    
    # From Sunset District:
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Mission District"): 25,
    
    # From Nob Hill:
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Mission District"): 13,
    
    # From Embarcadero:
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Mission District"): 20,
    
    # From Presidio:
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Mission District"): 26,
    
    # From Mission District:
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Presidio"): 25,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
#   x[i] is a Boolean indicating whether meeting friend i is scheduled.
#   start[i] is an integer representing the start time (minutes after 9:00AM at Pacific Heights).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow start times to take on a wide range.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival is at Pacific Heights at time = 0.
arrival_location = "Pacific Heights"
arrival_time = 0

# For each friend scheduled, enforce:
# - The meeting start must be no earlier than the friend’s available start.
# - The meeting must finish (start + duration) by the friend’s available end.
# - You must have time to travel from your arrival location to the friend’s location.
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
# For any two meetings scheduled, require that either meeting i (plus its duration and travel from its location to j) 
# is completed before meeting j begins, or vice versa.
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
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    # Sort the scheduled meetings by start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Pacific Heights):")
    # Helper function: Convert minutes relative to 9:00AM (540 minutes after midnight) into HH:MM.
    def format_time(m):
        total = 540 + m  # 540 minutes = 9:00AM.
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")