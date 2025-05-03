from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# The distances are directional.
travel = {
    # From Bayview:
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Pacific Heights"): 23,
    
    # From North Beach:
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    
    # From Nob Hill:
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    
    # From Union Square:
    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    
    # From Alamo Square:
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    
    # From Presidio:
    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    
    # From Chinatown:
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    
    # From Pacific Heights:
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimization model.
opt = Optimize()

# You arrive at Bayview at 9:00AM.
arrival_location = "Bayview"
arrival_time = 0  # minutes after 9:00AM

# Friend meeting parameters.
# Times are measured in minutes after 9:00AM.
# For each friend, we list the location, the available window, and the required meeting duration.
#
# Brian: at North Beach from 1:00PM to 7:00PM.
#   1:00PM => 240, 7:00PM => 600; duration = 90 minutes.
# Richard: at Fisherman's Wharf from 11:00AM to 12:45PM.
#   11:00AM => 120, 12:45PM => 225; duration = 60 minutes.
# Ashley: at Haight-Ashbury from 3:00PM to 8:30PM.
#   3:00PM => 360, 8:30PM => 690; duration = 90 minutes.
# Elizabeth: at Nob Hill from 11:45AM to 6:30PM.
#   11:45AM => 165, 6:30PM => 570; duration = 75 minutes.
# Jessica: at Golden Gate Park from 8:00PM to 9:45PM.
#   8:00PM => 660, 9:45PM => 765; duration = 105 minutes.
# Deborah: at Union Square from 5:30PM to 10:00PM.
#   5:30PM => 510, 10:00PM => 780; duration = 60 minutes.
# Kimberly: at Alamo Square from 5:30PM to 9:15PM.
#   5:30PM => 510, 9:15PM => 735; duration = 45 minutes.
# Matthew: at Presidio from 8:15AM to 9:00AM.
#   8:15AM => -45, 9:00AM => 0; duration = 15 minutes.
# Kenneth: at Chinatown from 1:45PM to 7:30PM.
#   1:45PM => 285, 7:30PM => 630; duration = 105 minutes.
# Anthony: at Pacific Heights from 2:15PM to 4:00PM.
#   2:15PM => 315, 4:00PM => 420; duration = 30 minutes.
friends = [
    {"name": "Brian",     "location": "North Beach",         "avail_start": 240, "avail_end": 600, "duration": 90},
    {"name": "Richard",   "location": "Fisherman's Wharf",   "avail_start": 120, "avail_end": 225, "duration": 60},
    {"name": "Ashley",    "location": "Haight-Ashbury",      "avail_start": 360, "avail_end": 690, "duration": 90},
    {"name": "Elizabeth", "location": "Nob Hill",            "avail_start": 165, "avail_end": 570, "duration": 75},
    {"name": "Jessica",   "location": "Golden Gate Park",    "avail_start": 660, "avail_end": 765, "duration": 105},
    {"name": "Deborah",   "location": "Union Square",        "avail_start": 510, "avail_end": 780, "duration": 60},
    {"name": "Kimberly",  "location": "Alamo Square",        "avail_start": 510, "avail_end": 735, "duration": 45},
    {"name": "Matthew",   "location": "Presidio",            "avail_start": -45, "avail_end": 0,   "duration": 15},
    {"name": "Kenneth",   "location": "Chinatown",           "avail_start": 285, "avail_end": 630, "duration": 105},
    {"name": "Anthony",   "location": "Pacific Heights",     "avail_start": 315, "avail_end": 420, "duration": 30},
]

num_friends = len(friends)

# The set of all relevant locations.
locations = [
    "Bayview",
    "North Beach",
    "Fisherman's Wharf",
    "Haight-Ashbury",
    "Nob Hill",
    "Golden Gate Park",
    "Union Square",
    "Alamo Square",
    "Presidio",
    "Chinatown",
    "Pacific Heights",
]

# Decision variables:
# For each friend i, we define:
#   x[i]: a Boolean indicating whether we schedule this meeting.
#   start[i]: an integer representing the start time of the meeting (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # We assume a wide domain for the meeting start times.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, enforce:
# 1. Meeting cannot start before the friend is available.
# 2. Meeting must finish (start + duration) before the availability window ends.
# 3. Enough time is allotted to travel from your arrival location (Bayview) to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For each pair of scheduled meetings, enforce that they do not overlap.
# For any two meetings i and j, if both are scheduled then either:
#   meeting i (finish time + travel time from i to j) <= meeting j start, OR
#   meeting j (finish time + travel time from j to i) <= meeting i start.
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
# Solve the scheduling problem and output the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM):")
    
    def format_time(minutes_after_9):
        # 9:00AM is 540 minutes after midnight.
        total = 540 + minutes_after_9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")