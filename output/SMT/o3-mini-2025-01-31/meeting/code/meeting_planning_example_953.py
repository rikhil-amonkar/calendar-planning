from z3 import *

# -----------------------------------------------------------------------------
# Travel distances between the various San Francisco locations (in minutes).
# The travel times are directional.
travel = {
    # From Embarcadero:
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "North Beach"): 5,
    
    # From The Castro:
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "North Beach"): 20,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "North Beach"): 23,
    
    # From Presidio:
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "North Beach"): 18,
    
    # From Sunset District:
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "North Beach"): 28,
    
    # From Nob Hill:
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "North Beach"): 8,
    
    # From Mission District:
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "North Beach"): 17,
    
    # From Richmond District:
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "North Beach"): 17,
    
    # From Financial District:
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
    
    # From Alamo Square:
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "North Beach"): 15,
    
    # From North Beach:
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Alamo Square"): 16,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimization model.
opt = Optimize()

# You arrive at Embarcadero at 9:00AM.
arrival_location = "Embarcadero"
arrival_time = 0  # minutes after 9:00AM

# Friend meeting parameters. All times are in minutes after 9:00AM.
# For each friend we record:
#   - meeting location,
#   - available time window (as [avail_start, avail_end]),
#   - and the required meeting duration.
# Times are computed by subtracting 540 (minutes after midnight for 9:00AM).
#
# Betty: at The Castro from 12:00PM to 2:45PM.
#   12:00PM -> 720 - 540 = 180;  2:45PM -> 885 - 540 = 345; duration = 45 minutes.
# Paul: at Golden Gate Park from 7:30AM to 8:15PM.
#   7:30AM -> 450 - 540 = -90; 8:15PM -> 12315? Let’s compute:
#     8:15PM is 20:15 -> 1215 - 540 = 675; duration = 90 minutes.
# William: at Presidio from 8:15AM to 2:45PM.
#   8:15AM -> 495 - 540 = -45; 2:45PM -> 885 - 540 = 345; duration = 90 minutes.
# James: at Sunset District from 7:00PM to 9:00PM.
#   7:00PM -> 1140 - 540 = 600; 9:00PM -> 1260 - 540 = 720; duration = 90 minutes.
# Emily: at Nob Hill from 7:15AM to 1:30PM.
#   7:15AM -> 435 - 540 = -105; 1:30PM -> 810 - 540 = 270; duration = 30 minutes.
# Ashley: at Mission District from 5:30PM to 8:30PM.
#   5:30PM -> 1050 - 540 = 510; 8:30PM -> 1230 - 540 = 690; duration = 120 minutes.
# Timothy: at Richmond District from 7:30PM to 10:00PM.
#   7:30PM -> 1170 - 540 = 630; 10:00PM -> 1320 - 540 = 780; duration = 45 minutes.
# Rebecca: at Financial District from 4:30PM to 6:00PM.
#   4:30PM -> 990 - 540 = 450; 6:00PM -> 1080 - 540 = 540; duration = 75 minutes.
# Andrew: at Alamo Square from 11:45AM to 12:45PM.
#   11:45AM -> 705 - 540 = 165; 12:45PM -> 765 - 540 = 225; duration = 45 minutes.
# Daniel: at North Beach from 4:30PM to 6:15PM.
#   4:30PM -> 990 - 540 = 450; 6:15PM -> 1095 - 540 = 555; duration = 45 minutes.

friends = [
    {"name": "Betty",   "location": "The Castro",        "avail_start": 180, "avail_end": 345, "duration": 45},
    {"name": "Paul",    "location": "Golden Gate Park",   "avail_start": -90, "avail_end": 675, "duration": 90},
    {"name": "William", "location": "Presidio",           "avail_start": -45, "avail_end": 345, "duration": 90},
    {"name": "James",   "location": "Sunset District",    "avail_start": 600, "avail_end": 720, "duration": 90},
    {"name": "Emily",   "location": "Nob Hill",           "avail_start": -105,"avail_end": 270, "duration": 30},
    {"name": "Ashley",  "location": "Mission District",   "avail_start": 510, "avail_end": 690, "duration": 120},
    {"name": "Timothy", "location": "Richmond District",  "avail_start": 630, "avail_end": 780, "duration": 45},
    {"name": "Rebecca", "location": "Financial District", "avail_start": 450, "avail_end": 540, "duration": 75},
    {"name": "Andrew",  "location": "Alamo Square",       "avail_start": 165, "avail_end": 225, "duration": 45},
    {"name": "Daniel",  "location": "North Beach",        "avail_start": 450, "avail_end": 555, "duration": 45},
]

num_friends = len(friends)

# All relevant locations.
locations = [
    "Embarcadero",
    "The Castro",
    "Golden Gate Park",
    "Presidio",
    "Sunset District",
    "Nob Hill",
    "Mission District",
    "Richmond District",
    "Financial District",
    "Alamo Square",
    "North Beach",
]

# Decision variables:
# For each friend i, we define:
#   x[i]: a Boolean variable that is True if we schedule the meeting.
#   start[i]: an integer variable for the start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)  # wide domain for start times

# For each friend meeting that is scheduled, enforce:
# 1. The meeting must start no earlier than the friend’s available start.
# 2. The meeting (start time + meeting duration) must end by the friend’s available end.
# 3. The meeting cannot start before you have traveled from your arrival location (Embarcadero)
#    to the meeting location.
for i, friend in enumerate(friends):
    d = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + d <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For every pair of meetings that are both scheduled, ensure they do not overlap.
# That is, either meeting i, including its duration and travel time to meeting j's location,
# ends before meeting j starts, or vice versa.
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

# Set the objective to maximize the number of scheduled meetings.
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
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")