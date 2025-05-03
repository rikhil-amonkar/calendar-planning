from z3 import *

# ---------------------------
# Data definitions
# ---------------------------
# We represent time in minutes after 9:00AM. 
# The available windows for the meetings are provided in these terms.
# Note: If a friend’s availability begins before 9:00AM, we use the actual time (e.g. Patricia’s 7:15AM becomes -105 minutes)
# because the travel constraint from our starting location (Embarcadero) will force a later start.

# Friends meeting definitions:
# 1. Helen: at Marina District from 10:30AM to 1:00PM.
#    -> 10:30AM is 90 minutes after 9:00AM; 1:00PM is 240 minutes. Minimum meeting: 120 minutes.
# 2. Jeffrey: at Richmond District from 8:45PM to 9:30PM.
#    -> 8:45PM is 705 minutes after 9:00AM; 9:30PM is 750 minutes. Minimum meeting: 45 minutes.
# 3. Sarah: at The Castro from 3:30PM to 7:15PM.
#    -> 3:30PM is 390 minutes; 7:15PM is 615 minutes. Minimum meeting: 120 minutes.
# 4. Deborah: at Pacific Heights from 7:00PM to 9:15PM.
#    -> 7:00PM is 600 minutes; 9:15PM is 735 minutes. Minimum meeting: 120 minutes.
# 5. Ronald: at Golden Gate Park from 11:15AM to 5:45PM.
#    -> 11:15AM is 135 minutes; 5:45PM is 525 minutes. Minimum meeting: 120 minutes.
# 6. Thomas: at Haight-Ashbury from 2:45PM to 8:00PM.
#    -> 2:45PM is 345 minutes; 8:00PM is 660 minutes. Minimum meeting: 75 minutes.
# 7. Patricia: at Russian Hill from 7:15AM to 12:30PM.
#    -> 7:15AM is -105 minutes; 12:30PM is 210 minutes. Minimum meeting: 30 minutes.
# 8. Jason: at Sunset District from 3:30PM to 9:30PM.
#    -> 3:30PM is 390 minutes; 9:30PM is 750 minutes. Minimum meeting: 75 minutes.
# 9. Nancy: at Financial District from 6:00PM to 9:00PM.
#    -> 6:00PM is 540 minutes; 9:00PM is 720 minutes. Minimum meeting: 75 minutes.
# 10. Kimberly: at Presidio from 12:15PM to 2:15PM.
#     -> 12:15PM is 195 minutes; 2:15PM is 375 minutes. Minimum meeting: 90 minutes.

friends = [
    {"name": "Helen",    "location": "Marina District",    "avail_start": 90,   "avail_end": 240, "duration": 120},
    {"name": "Jeffrey",  "location": "Richmond District",  "avail_start": 705,  "avail_end": 750, "duration": 45},
    {"name": "Sarah",    "location": "The Castro",         "avail_start": 390,  "avail_end": 615, "duration": 120},
    {"name": "Deborah",  "location": "Pacific Heights",    "avail_start": 600,  "avail_end": 735, "duration": 120},
    {"name": "Ronald",   "location": "Golden Gate Park",   "avail_start": 135,  "avail_end": 525, "duration": 120},
    {"name": "Thomas",   "location": "Haight-Ashbury",     "avail_start": 345,  "avail_end": 660, "duration": 75},
    {"name": "Patricia", "location": "Russian Hill",       "avail_start": -105, "avail_end": 210, "duration": 30},
    {"name": "Jason",    "location": "Sunset District",    "avail_start": 390,  "avail_end": 750, "duration": 75},
    {"name": "Nancy",    "location": "Financial District", "avail_start": 540,  "avail_end": 720, "duration": 75},
    {"name": "Kimberly", "location": "Presidio",           "avail_start": 195,  "avail_end": 375, "duration": 90},
]

# All locations (our starting location as well as friends’ meeting spots):
locations = ["Embarcadero", "Marina District", "Richmond District", "The Castro",
             "Pacific Heights", "Golden Gate Park", "Haight-Ashbury", "Russian Hill",
             "Sunset District", "Financial District", "Presidio"]

# Travel times between locations (in minutes). They are defined as (origin, destination): travel time.
travel = {
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Presidio"): 20,

    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Presidio"): 10,

    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Presidio"): 7,

    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Presidio"): 20,

    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Presidio"): 11,

    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Presidio"): 11,

    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Presidio"): 15,

    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Presidio"): 14,

    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Presidio"): 16,

    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Presidio"): 22,

    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Financial District"): 23,
}

def get_travel_time(origin, destination):
    # Returns travel time between origin and destination.
    return travel[(origin, destination)]

# -----------------------------
# Z3 Model
# -----------------------------
# We use Optimize to maximize the number of scheduled meetings.
opt = Optimize()

num_friends = len(friends)

# Decision variables:
# - x[i]: Boolean variable indicating if we schedule a meeting with friend i.
# - start[i]: Integer variable for the meeting’s start time (minutes after 9:00AM)
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Add reasonable bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -200, start[i] <= 1000)

# Starting location and arrival time.
# You arrive at Embarcadero at 9:00AM (i.e. time 0).
start_location = "Embarcadero"
arrival_time = 0

# For each friend scheduled, enforce:
#   (a) Meeting start is no earlier than friend’s available start.
#   (b) Meeting (start + duration) finishes before friend’s available end.
#   (c) Meeting start must be no earlier than arrival_time + travel_time (from Embarcadero).
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(start_location, loc)
    
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Non-overlap constraints:
# For any two scheduled meetings, ensure that (meeting_i + travel_time(i->j)) finishes before meeting_j starts,
# OR (meeting_j + travel_time(j->i)) finishes before meeting_i starts.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        no_overlap = Or(start[i] + dur_i + travel_i_j <= start[j],
                        start[j] + dur_j + travel_j_i <= start[i])
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: Maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------
# Solve and Print the Schedule
# -----------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            st = model.evaluate(start[i]).as_long()
            schedule.append((st, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for st, name, loc, dur in schedule:
        finish = st + dur
        # Helper to convert minutes since 9:00AM to hh:mm.
        def to_time(minutes):
            total = 9*60 + minutes
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc} from {to_time(st)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")