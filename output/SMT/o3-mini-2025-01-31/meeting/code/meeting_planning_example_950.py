from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From The Castro:
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Union Square"): 19,
    
    # From Financial District:
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Union Square"): 9,
    
    # From Sunset District:
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Union Square"): 30,
    
    # From Russian Hill:
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Union Square"): 10,
    
    # From Mission District:
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Union Square"): 15,
    
    # From Marina District:
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Union Square"): 16,
    
    # From Presidio:
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Union Square"): 22,
    
    # From Bayview:
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Union Square"): 18,
    
    # From North Beach:
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Union Square"): 7,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Union Square"): 13,
    
    # From Union Square:
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimization model.
opt = Optimize()

# Arrival: You arrive at The Castro at 9:00AM (time = 0).
arrival_location = "The Castro"
arrival_time = 0

# Define friend meeting constraints.
# Times are in minutes after 9:00AM.
# Mary: at Financial District from 2:15PM to 4:45PM ->
#       2:15PM = 14:15, so 14:15-9:00 = 315 minutes,
#       4:45PM = 16:45, so 16:45-9:00 = 465 minutes; minimum duration: 75 minutes.
# Mark: at Sunset District from 7:45PM to 10:00PM ->
#       7:45PM = 19:45, so 19:45-9:00 = 645 minutes,
#       10:00PM = 22:00, so 22:00-9:00 = 780 minutes; minimum duration: 105 minutes.
# Steven: at Russian Hill from 11:30AM to 7:45PM ->
#       11:30AM = 11:30-9:00 = 150 minutes,
#       7:45PM = 19:45-9:00 = 645 minutes; minimum duration: 90 minutes.
# Lisa: at Mission District from 1:30PM to 5:30PM ->
#       1:30PM = 13:30-9:00 = 270 minutes,
#       5:30PM = 17:30-9:00 = 510 minutes; minimum duration: 15 minutes.
# Matthew: at Marina District from 7:30AM to 5:45PM ->
#       7:30AM = 7:30-9:00 = -90 minutes,
#       5:45PM = 17:45-9:00 = 525 minutes; minimum duration: 30 minutes.
# Joshua: at Presidio from 7:30AM to 7:45PM ->
#       7:30AM = -90 minutes,
#       7:45PM = 19:45-9:00 = 645 minutes; minimum duration: 120 minutes.
# Margaret: at Bayview from 9:30AM to 6:00PM ->
#       9:30AM = 30 minutes,
#       6:00PM = 18:00-9:00 = 540 minutes; minimum duration: 120 minutes.
# Robert: at North Beach from 10:00AM to 4:45PM ->
#       10:00AM = 60 minutes,
#       4:45PM = 16:45-9:00 = 465 minutes; minimum duration: 120 minutes.
# Brian: at Fisherman's Wharf from 5:30PM to 6:30PM ->
#       5:30PM = 17:30-9:00 = 510 minutes,
#       6:30PM = 18:30-9:00 = 570 minutes; minimum duration: 30 minutes.
# Melissa: at Union Square from 7:30PM to 9:00PM ->
#       7:30PM = 19:30-9:00 = 630 minutes,
#       9:00PM = 21:00-9:00 = 720 minutes; minimum duration: 90 minutes.
friends = [
    {"name": "Mary",     "location": "Financial District", "avail_start": 315, "avail_end": 465, "duration": 75},
    {"name": "Mark",     "location": "Sunset District",      "avail_start": 645, "avail_end": 780, "duration": 105},
    {"name": "Steven",   "location": "Russian Hill",         "avail_start": 150, "avail_end": 645, "duration": 90},
    {"name": "Lisa",     "location": "Mission District",     "avail_start": 270, "avail_end": 510, "duration": 15},
    {"name": "Matthew",  "location": "Marina District",      "avail_start": -90, "avail_end": 525, "duration": 30},
    {"name": "Joshua",   "location": "Presidio",             "avail_start": -90, "avail_end": 645, "duration": 120},
    {"name": "Margaret", "location": "Bayview",              "avail_start": 30,  "avail_end": 540, "duration": 120},
    {"name": "Robert",   "location": "North Beach",          "avail_start": 60,  "avail_end": 465, "duration": 120},
    {"name": "Brian",    "location": "Fisherman's Wharf",    "avail_start": 510, "avail_end": 570, "duration": 30},
    {"name": "Melissa",  "location": "Union Square",         "avail_start": 630, "avail_end": 720, "duration": 90},
]

num_friends = len(friends)

# Define the relevant locations.
locations = [
    "The Castro",
    "Financial District",
    "Sunset District",
    "Russian Hill",
    "Mission District",
    "Marina District",
    "Presidio",
    "Bayview",
    "North Beach",
    "Fisherman's Wharf",
    "Union Square",
]

# Decision variables:
# For each friend i:
#   x[i] : Boolean indicating if the meeting is scheduled.
#   start[i] : Integer representing the start time (minutes after 9:00AM) of the meeting.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Use a broad domain for meeting start times.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For every scheduled meeting, enforce:
# - The meeting doesn't start before the friend is available.
# - The meeting (start time + duration) finishes by the friend’s available end.
# - There's enough time to travel from arrival (The Castro) to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For each pair of scheduled meetings, ensure they do not clash.
# That is, for any two meetings i and j (if both are scheduled) either:
# meeting i, plus its duration and travel time from i's location to j's location finishes before j starts,
# or meeting j (plus its own duration and travel time from j to i) finishes before i starts.
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

# Set the objective: maximize the number of meetings scheduled.
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
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM):")
    def format_time(minutes_after_9):
        # 9:00AM is 540 minutes after midnight.
        total = 540 + minutes_after_9
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")