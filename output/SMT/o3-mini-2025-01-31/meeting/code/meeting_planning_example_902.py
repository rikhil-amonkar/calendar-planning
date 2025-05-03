from z3 import *

# ---------------------------
# Data definitions
# ---------------------------

# We measure time in minutes after 9:00AM.
# Friend meeting data: name, location, available start time (minutes after 9:00AM),
# available end time, and required meeting duration.
# Times are computed as follows:
#   9:00AM -> 0
#   For example, 3:15PM is 6h15 after 9:00, i.e. 375 minutes.
# The friend data below:
friends = [
    {"name": "Lisa",     "location": "Alamo Square",      "avail_start": 375, "avail_end": 615, "duration": 45},  # 3:15PM to 7:15PM
    {"name": "George",   "location": "Bayview",           "avail_start": 600, "avail_end": 780, "duration": 30},  # 7:00PM to 10:00PM
    {"name": "Steven",   "location": "Pacific Heights",   "avail_start": 30,  "avail_end": 405, "duration": 15},  # 9:30AM to 3:45PM
    {"name": "Nancy",    "location": "Nob Hill",          "avail_start": 570, "avail_end": 735, "duration": 60},  # 6:30PM to 9:15PM
    {"name": "Emily",    "location": "North Beach",       "avail_start": 390, "avail_end": 480, "duration": 45},  # 3:30PM to 5:00PM
    {"name": "Anthony",  "location": "Chinatown",         "avail_start": 405, "avail_end": 495, "duration": 45},  # 3:45PM to 5:15PM
    {"name": "John",     "location": "Financial District","avail_start": 375, "avail_end": 705, "duration": 90},  # 3:15PM to 8:45PM
    {"name": "Timothy",  "location": "Sunset District",   "avail_start": 15,  "avail_end": 525, "duration": 75},  # 9:15AM to 5:45PM
    {"name": "David",    "location": "Haight-Ashbury",    "avail_start": 270, "avail_end": 705, "duration": 60},  # 1:30PM to 8:45PM
    {"name": "Betty",    "location": "Union Square",      "avail_start": 345, "avail_end": 735, "duration": 45}   # 2:45PM to 9:15PM
]

# List of all locations (including our starting location "Embarcadero").
locations = ["Embarcadero", "Alamo Square", "Bayview", "Pacific Heights",
             "Nob Hill", "North Beach", "Chinatown", "Financial District",
             "Sunset District", "Haight-Ashbury", "Union Square"]

# Travel times (in minutes) between locations as given.
# Each tuple (origin, destination) maps to the travel time.
travel = {
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,

    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Union Square"): 14,

    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Union Square"): 18,

    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,

    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Union Square"): 7,

    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,

    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,

    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Union Square"): 9,

    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Union Square"): 30,

    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Union Square"): 19,

    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Haight-Ashbury"): 18,
}

def get_travel_time(orig, dest):
    # Return the travel time; assume the key exists.
    return travel[(orig, dest)]

# -----------------------------
# Z3 Model
# -----------------------------

# Create an optimizer (for maximizing the number of meetings).
opt = Optimize()

n = len(friends)

# Decision variables:
# For each friend i, x[i] is a Bool indicating whether we schedule that meeting.
# start[i] is the start time (in minutes after 9:00AM) at which the meeting is scheduled.
x = [Bool(f"x_{i}") for i in range(n)]
start = [Int(f"start_{i}") for i in range(n)]

# Allow a wide range for meeting start times.
for i in range(n):
    opt.add(start[i] >= -100, start[i] <= 1000)

# The starting location is Embarcadero at 9:00AM (time = 0).
start_location = "Embarcadero"
arrival_time = 0

# For each friend meeting, if scheduled then constrain:
#   (a) The meeting start is at or after the friend’s available start time.
#   (b) The meeting end (start + duration) is no later than the friend’s available end time.
#   (c) The meeting start is no earlier than when you can get there (arrival_time +
#       travel time from the starting location, Embarcadero).
for i, f in enumerate(friends):
    dur = f["duration"]
    availS = f["avail_start"]
    availE = f["avail_end"]
    loc = f["location"]
    travel_from_start = get_travel_time(start_location, loc)
    opt.add(Implies(x[i], start[i] >= availS))
    opt.add(Implies(x[i], start[i] + dur <= availE))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Add non-overlap constraints: For any two meetings i and j (if both scheduled),
# either meeting i (plus its duration and travel time from its location to j's)
# must finish not later than meeting j starts, or vice-versa.
for i in range(n):
    for j in range(i+1, n):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        cond = Or(start[i] + dur_i + travel_i_j <= start[j],
                  start[j] + dur_j + travel_j_i <= start[i])
        opt.add(Implies(And(x[i], x[j]), cond))

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(n)]))

# -----------------------------
# Solve the model
# -----------------------------
if opt.check() == sat:
    m = opt.model()
    scheduled_meetings = []
    for i in range(n):
        if m.evaluate(x[i]):
            st = m.evaluate(start[i]).as_long()
            scheduled_meetings.append((st, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    scheduled_meetings.sort(key=lambda t: t[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for st, name, loc, dur in scheduled_meetings:
        finish = st + dur
        def to_time(minutes):
            # Convert minutes after 9:00AM into hh:mm format.
            total = 9 * 60 + minutes
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc}: from {to_time(st)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")