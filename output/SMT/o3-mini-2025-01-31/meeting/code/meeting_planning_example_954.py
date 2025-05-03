from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes). The keys are (origin, destination) pairs.
travel = {
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Sunset District"): 27,
    
    # From Pacific Heights:
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Sunset District"): 21,
    
    # From The Castro:
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Sunset District"): 17,
    
    # From Financial District:
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Sunset District"): 30,
    
    # From Embarcadero:
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Sunset District"): 30,
    
    # From Russian Hill:
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Sunset District"): 23,
    
    # From North Beach:
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Sunset District"): 27,
    
    # From Marina District:
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Sunset District"): 19,
    
    # From Bayview:
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Sunset District"): 23,
    
    # From Alamo Square:
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Sunset District"): 16,
    
    # From Sunset District:
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Alamo Square"): 17,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimization model.
opt = Optimize()

# You arrive at Fisherman's Wharf at 9:00AM.
arrival_location = "Fisherman's Wharf"
arrival_time = 0  # minutes after 9:00AM

# Meeting parameters for each friend.
# All times below are in minutes after 9:00AM.
# The times have been computed by converting the given clock times.
#
# Robert: at Pacific Heights from 3:15PM to 7:45PM.
#   3:15PM => 15*60+15 = 915, 7:45PM => 19*60+45 = 1185, minus 540 gives [375, 645]; duration = 45.
# Brian: at The Castro from 1:15PM to 4:30PM.
#   1:15PM => 13*60+15 = 795, 4:30PM => 16*60+30 = 990, minus 540 gives [255, 450]; duration = 90.
# Matthew: at Financial District from 7:45PM to 9:15PM.
#   7:45PM => 19*60+45 = 1185, 9:15PM => 21*60+15 = 1275, minus 540 gives [645, 735]; duration = 45.
# John: at Embarcadero from 3:30PM to 6:15PM.
#   3:30PM => 15*60+30 = 930, 6:15PM => 18*60+15 = 1095, minus 540 gives [390, 555]; duration = 105.
# Kenneth: at Russian Hill from 8:00AM to 12:00PM.
#   8:00AM => 480, 12:00PM => 720, minus 540 gives [-60, 180]; duration = 75.
# Joshua: at North Beach from 8:15AM to 7:30PM.
#   8:15AM => 495, 7:30PM => 1170, minus 540 gives [-45, 630]; duration = 105.
# Lisa: at Marina District from 11:30AM to 5:45PM.
#   11:30AM => 690, 5:45PM => 1065, minus 540 gives [150, 525]; duration = 120.
# Emily: at Bayview from 6:30PM to 8:15PM.
#   6:30PM => 18*60+30 = 1110, 8:15PM => 20*60+15 = 1215, minus 540 gives [570, 675]; duration = 60.
# Elizabeth: at Alamo Square from 8:00AM to 4:45PM.
#   8:00AM => 480, 4:45PM => 16*60+45 = 1005, minus 540 gives [-60, 465]; duration = 105.
# Helen: at Sunset District from 7:15AM to 10:30AM.
#   7:15AM => 435, 10:30AM => 630, minus 540 gives [-105, 90]; duration = 120.
friends = [
    {"name": "Robert",     "location": "Pacific Heights",   "avail_start": 375, "avail_end": 645, "duration": 45},
    {"name": "Brian",      "location": "The Castro",        "avail_start": 255, "avail_end": 450, "duration": 90},
    {"name": "Matthew",    "location": "Financial District","avail_start": 645, "avail_end": 735, "duration": 45},
    {"name": "John",       "location": "Embarcadero",       "avail_start": 390, "avail_end": 555, "duration": 105},
    {"name": "Kenneth",    "location": "Russian Hill",      "avail_start": -60, "avail_end": 180, "duration": 75},
    {"name": "Joshua",     "location": "North Beach",       "avail_start": -45, "avail_end": 630, "duration": 105},
    {"name": "Lisa",       "location": "Marina District",   "avail_start": 150, "avail_end": 525, "duration": 120},
    {"name": "Emily",      "location": "Bayview",           "avail_start": 570, "avail_end": 675, "duration": 60},
    {"name": "Elizabeth",  "location": "Alamo Square",      "avail_start": -60, "avail_end": 465, "duration": 105},
    {"name": "Helen",      "location": "Sunset District",   "avail_start": -105,"avail_end": 90,  "duration": 120},
]

num_friends = len(friends)

# A list of all locations involved.
locations = [
    "Fisherman's Wharf",
    "Pacific Heights",
    "The Castro",
    "Financial District",
    "Embarcadero",
    "Russian Hill",
    "North Beach",
    "Marina District",
    "Bayview",
    "Alamo Square",
    "Sunset District",
]

# Decision variables:
# For each friend i, we define:
#   - x[i]: a Boolean variable that is True if you meet that friend.
#   - start[i]: an integer variable that represents the start time of the meeting (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each friend meeting that is scheduled, enforce:
# 1. The meeting must start no earlier than the friend's available start.
# 2. The meeting (start time + required duration) must end by the friend's available end.
# 3. The meeting must start no earlier than the arrival time plus travel time from the arrival location (Fisherman's Wharf)
#    to the friend's meeting location.
for i, friend in enumerate(friends):
    d = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + d <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For every pair of scheduled meetings, enforce non-overlap.
# That is, if meetings i and j are both scheduled then either meeting i (plus its duration and travel time from i to j)
# is finished before meeting j starts, or vice-versa.
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

# Set the objective: maximize the number of meetings scheduled.
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
    def format_time(minutes_after9):
        # 9:00AM is 540 minutes after midnight.
        total = 540 + minutes_after9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, d in schedule:
        finish = s_time + d
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {d} mins)")
else:
    print("No feasible schedule found.")