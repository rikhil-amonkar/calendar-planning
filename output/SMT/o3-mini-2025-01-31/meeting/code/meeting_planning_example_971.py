from z3 import *

# -------------------------------------------------------------------------
# Travel distances (in minutes) between neighborhoods.
# Note: These are directional and not necessarily symmetric.
travel = {
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Union Square"): 7,

    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Union Square"): 19,

    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,

    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Union Square"): 21,

    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Union Square"): 14,

    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Union Square"): 22,

    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Union Square"): 16,

    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Union Square"): 10,

    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Union Square"): 19,

    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,

    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Chinatown"): 7,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -------------------------------------------------------------------------
# Create the Z3 optimizer
opt = Optimize()

# You arrive at Nob Hill at 9:00AM.
arrival_location = "Nob Hill"
arrival_time = 0  # in minutes after 9:00AM

# Friend meeting data.
# Times are expressed as minutes relative to 9:00AM.
# Negative values denote times before 9:00AM.
friends = [
    # Sarah: at The Castro from 9:30AM to 3:15PM; meeting ≥45 minutes.
    {"name": "Sarah", "location": "The Castro", "avail_start": 30, "avail_end": 375, "duration": 45},
    # Melissa: at Financial District from 12:30PM to 4:30PM; meeting ≥90 minutes.
    {"name": "Melissa", "location": "Financial District", "avail_start": 210, "avail_end": 450, "duration": 90},
    # Lisa: at Richmond District from 6:30PM to 7:45PM; meeting ≥75 minutes.
    {"name": "Lisa", "location": "Richmond District", "avail_start": 570, "avail_end": 645, "duration": 75},
    # Rebecca: at Alamo Square from 7:30AM to 7:45PM; meeting ≥75 minutes.
    {"name": "Rebecca", "location": "Alamo Square", "avail_start": -90, "avail_end": 645, "duration": 75},
    # Kenneth: at Presidio from 1:45PM to 4:30PM; meeting ≥75 minutes.
    {"name": "Kenneth", "location": "Presidio", "avail_start": 285, "avail_end": 450, "duration": 75},
    # Jessica: at Marina District from 5:00PM to 8:00PM; meeting ≥15 minutes.
    {"name": "Jessica", "location": "Marina District", "avail_start": 480, "avail_end": 660, "duration": 15},
    # John: at Russian Hill from 3:00PM to 7:45PM; meeting ≥60 minutes.
    {"name": "John", "location": "Russian Hill", "avail_start": 360, "avail_end": 645, "duration": 60},
    # Ronald: at Haight-Ashbury from 4:00PM to 10:00PM; meeting ≥120 minutes.
    {"name": "Ronald", "location": "Haight-Ashbury", "avail_start": 420, "avail_end": 780, "duration": 120},
    # David: at Chinatown from 2:45PM to 9:00PM; meeting ≥45 minutes.
    {"name": "David", "location": "Chinatown", "avail_start": 345, "avail_end": 720, "duration": 45},
    # James: at Union Square from 8:45AM to 3:30PM; meeting ≥60 minutes.
    {"name": "James", "location": "Union Square", "avail_start": -15, "avail_end": 390, "duration": 60},
]

num_friends = len(friends)

# List of relevant locations.
locations = ["Nob Hill", "The Castro", "Financial District", "Richmond District", 
             "Alamo Square", "Presidio", "Marina District", "Russian Hill", 
             "Haight-Ashbury", "Chinatown", "Union Square"]

# Decision variables:
# For each friend, x[i] is a Boolean indicating if that meeting is scheduled.
# start[i] is the meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # limits on the start time (arbitrary bounds)
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each meeting, if scheduled, enforce:
# (a) Meeting starts no earlier than the friend’s available start.
# (b) Meeting ends (start + duration) by the friend’s available end.
# (c) Meeting can only start after you travel from Nob Hill to that friend's location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    # travel time from your starting location (Nob Hill) to the friend’s location.
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Non-overlap constraints:
# For any two scheduled meetings, ensure that one meeting finishes (plus travel time)
# before the other starts.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        # travel times from meeting i location to j location and vice versa:
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        no_overlap = Or(
            start[i] + dur_i + travel_i_j <= start[j],
            start[j] + dur_j + travel_j_i <= start[i]
        )
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -------------------------------------------------------------------------
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00 AM):")
    
    def format_time(minutes_after_9):
        # 9:00 AM is 540 minutes after midnight.
        total = 540 + minutes_after_9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")