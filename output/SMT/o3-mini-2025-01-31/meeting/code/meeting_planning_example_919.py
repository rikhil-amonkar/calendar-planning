from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
# All times are relative to your arrival at Fisherman's Wharf at 9:00AM (time = 0):
#
# 1. Matthew at Chinatown from 2:30PM to 6:00PM; minimum meeting = 90 minutes.
#    Window: [330, 540]
# 2. Elizabeth at Golden Gate Park from 8:15AM to 10:45AM; minimum meeting = 120 minutes.
#    Window: [-45, 105]
# 3. Patricia at Richmond District from 11:45AM to 5:30PM; minimum meeting = 45 minutes.
#    Window: [165, 510]
# 4. Kimberly at Mission District from 10:45AM to 12:00PM; minimum meeting = 15 minutes.
#    Window: [105, 180]
# 5. Robert at Bayview from 6:45PM to 7:45PM; minimum meeting = 15 minutes.
#    Window: [585, 645]
# 6. Sandra at Nob Hill from 9:15AM to 8:00PM; minimum meeting = 45 minutes.
#    Window: [15, 660]
# 7. James at Russian Hill from 9:00AM to 1:45PM; minimum meeting = 105 minutes.
#    Window: [0, 285]
# 8. Rebecca at Financial District from 8:15AM to 7:45PM; minimum meeting = 75 minutes.
#    Window: [-45, 630]
# 9. Andrew at Haight-Ashbury from 3:45PM to 7:15PM; minimum meeting = 120 minutes.
#    Window: [405, 615]
# 10. Mark at The Castro from 4:45PM to 8:00PM; minimum meeting = 30 minutes.
#    Window: [465, 660]
friends = [
    {"name": "Matthew",   "location": "Chinatown",         "avail_start": 330, "avail_end": 540, "duration": 90},
    {"name": "Elizabeth", "location": "Golden Gate Park",  "avail_start": -45, "avail_end": 105, "duration": 120},
    {"name": "Patricia",  "location": "Richmond District", "avail_start": 165, "avail_end": 510, "duration": 45},
    {"name": "Kimberly",  "location": "Mission District",  "avail_start": 105, "avail_end": 180, "duration": 15},
    {"name": "Robert",    "location": "Bayview",           "avail_start": 585, "avail_end": 645, "duration": 15},
    {"name": "Sandra",    "location": "Nob Hill",          "avail_start": 15,  "avail_end": 660, "duration": 45},
    {"name": "James",     "location": "Russian Hill",      "avail_start": 0,   "avail_end": 285, "duration": 105},
    {"name": "Rebecca",   "location": "Financial District","avail_start": -45, "avail_end": 630, "duration": 75},
    {"name": "Andrew",    "location": "Haight-Ashbury",    "avail_start": 405, "avail_end": 615, "duration": 120},
    {"name": "Mark",      "location": "The Castro",        "avail_start": 465, "avail_end": 660, "duration": 30},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Fisherman's Wharf",
    "Chinatown",
    "Golden Gate Park",
    "Richmond District",
    "Mission District",
    "Bayview",
    "Nob Hill",
    "Russian Hill",
    "Financial District",
    "Haight-Ashbury",
    "The Castro",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes)
# The keys are (origin, destination) tuples.
travel = {
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "The Castro"): 27,

    # From Chinatown:
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "The Castro"): 22,

    # From Golden Gate Park:
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "The Castro"): 13,

    # From Richmond District:
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "The Castro"): 16,

    # From Mission District:
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "The Castro"): 7,

    # From Bayview:
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "The Castro"): 19,

    # From Nob Hill:
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "The Castro"): 17,

    # From Russian Hill:
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "The Castro"): 21,

    # From Financial District:
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "The Castro"): 20,

    # From Haight-Ashbury:
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "The Castro"): 6,

    # From The Castro:
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Haight-Ashbury"): 6,
}

# Helper function to get the travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize() to maximize the total number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For friend i, x[i] is a Boolean that is True if the meeting is scheduled,
# and start[i] is the meeting start time (in minutes relative to 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Your arrival location is Fisherman's Wharf at time 0.
starting_location = "Fisherman's Wharf"
arrival_time = 0

# For each friend meeting (if scheduled) enforce:
#   - The meeting start is no earlier than the friend's available start.
#   - The meeting end (start + duration) is no later than the friend's available end.
#   - There is enough travel time from Fisherman's Wharf.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(starting_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Add pairwise non-overlap constraints.
# For any two meetings i and j that are both scheduled, ensure that either:
# meeting i (plus its duration and travel time from its location to j's) finishes
# before meeting j starts, or vice versa.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        dur_i = friends[i]["duration"]
        dur_j = friends[j]["duration"]
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = get_travel_time(loc_i, loc_j)
        travel_j_i = get_travel_time(loc_j, loc_i)
        no_overlap = Or(
            start[i] + dur_i + travel_i_j <= start[j],
            start[j] + dur_j + travel_j_i <= start[i]
        )
        opt.add(Implies(And(x[i], x[j]), no_overlap))

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the schedule.
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            t = model.evaluate(start[i]).as_long()
            schedule.append((t, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            total = 540 + minutes  # 9:00AM is 540 minutes after midnight.
            hr = total // 60
            mn = total % 60
            return f"{hr:02d}:{mn:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")