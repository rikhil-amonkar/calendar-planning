from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
travel = {
    # North Beach distances
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Russian Hill"): 4,
    # Chinatown distances
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Russian Hill"): 7,
    # Mission District distances
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Russian Hill"): 15,
    # Financial District distances
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Russian Hill"): 11,
    # Sunset District distances
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Russian Hill"): 24,
    # Pacific Heights distances
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Russian Hill"): 7,
    # Bayview distances
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Russian Hill"): 23,
    # The Castro distances
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Russian Hill"): 18,
    # Presidio distances
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Russian Hill"): 14,
    # Richmond District distances
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Russian Hill"): 13,
    # Russian Hill distances
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Richmond District"): 14,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at North Beach at 9:00AM.
arrival_location = "North Beach"
arrival_time = 0  # minutes after 9:00AM

# Friend meeting data.
# All times are in minutes after 9:00AM.
# (Negative times indicate times before 9:00AM.)
friends = [
    {"name": "Robert",   "location": "Chinatown",         "avail_start": 705, "avail_end": 780, "duration": 60},  # 8:45PM to 10:00PM (705 to 780)
    {"name": "Amanda",   "location": "Mission District",  "avail_start": 90,  "avail_end": 240, "duration": 60},  # 10:30AM to 1:00PM (90 to 240)
    {"name": "Margaret", "location": "Financial District","avail_start": 720, "avail_end": 765, "duration": 45},  # 9:00PM to 9:45PM (720 to 765)
    {"name": "Joseph",   "location": "Sunset District",   "avail_start": 135, "avail_end": 480, "duration": 105}, # 11:15AM to 5:00PM (135 to 480)
    {"name": "Jessica",  "location": "Pacific Heights",   "avail_start": 345, "avail_end": 465, "duration": 90},  # 2:45PM to 4:45PM (345 to 465)
    {"name": "Michelle", "location": "Bayview",           "avail_start": 570, "avail_end": 690, "duration": 105}, # 6:30PM to 8:30PM (570 to 690)
    {"name": "Mark",     "location": "The Castro",        "avail_start": 150, "avail_end": 435, "duration": 120}, # 11:30AM to 4:15PM (150 to 435)
    {"name": "Kevin",    "location": "Presidio",          "avail_start": 690, "avail_end": 780, "duration": 90},  # 8:30PM to 10:00PM (690 to 780)
    {"name": "Carol",    "location": "Richmond District", "avail_start": -30, "avail_end": 240, "duration": 90},  # 8:30AM to 1:00PM ( -30 to 240 )
    {"name": "David",    "location": "Russian Hill",      "avail_start": 195, "avail_end": 765, "duration": 75},  # 12:15PM to 9:45PM (195 to 765)
]

num_friends = len(friends)

# List of locations used.
locations = [
    "North Beach",
    "Chinatown",
    "Mission District",
    "Financial District",
    "Sunset District",
    "Pacific Heights",
    "Bayview",
    "The Castro",
    "Presidio",
    "Richmond District",
    "Russian Hill",
]

# Decision variables
# For each friend i, we have:
#   x[i]: Boolean variable to decide if the meeting is scheduled.
#   start[i]: Integer start time (minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow a wide range for possible start times.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, enforce:
# 1. The meeting must start no earlier than the friend’s available start.
# 2. The meeting must finish (start + duration) by the friend’s available end.
# 3. The meeting cannot start before you can travel from the arrival location (North Beach) to the friend's location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Add non-overlap constraints.
# For any two scheduled meetings i and j, ensure that the meeting i (plus its duration and travel time to j)
# ends before j starts, or vice versa.
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

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the scheduling problem and print the itinerary.
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
        # 9:00AM is 540 minutes after midnight
        total = 540 + minutes_after9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")