from z3 import *

# ---------------------------------------------------------------------
# Friend definitions:
#
# Times are measured in minutes after 9:00AM.
#
# Convert each friend’s availability window relative to 9:00AM:
# 1. Helen at Union Square: 11:00AM to 2:30PM becomes [120, 330] minutes,
#    and min meeting duration is 45 minutes.
# 2. Sandra at Sunset District: 7:45PM to 9:15PM becomes [645, 735] minutes,
#    and min meeting duration is 90 minutes.
# 3. Joseph at Nob Hill: 8:00PM to 9:15PM becomes [660, 735] minutes,
#    and min meeting duration is 75 minutes.
# 4. Jason at Bayview: 2:15PM to 7:00PM becomes [315, 600] minutes,
#    and min meeting duration is 90 minutes.
# 5. Sarah at Financial District: 2:30PM to 7:00PM becomes [330, 600] minutes,
#    and min meeting duration is 90 minutes.
# 6. Robert at Haight-Ashbury: 10:00AM to 4:00PM becomes [60, 420] minutes,
#    and min meeting duration is 105 minutes.
# 7. Carol at Pacific Heights: 2:45PM to 8:45PM becomes [345, 705] minutes,
#    and min meeting duration is 75 minutes.
# 8. Michelle at Golden Gate Park: 2:45PM to 6:00PM becomes [345, 540] minutes,
#    and min meeting duration is 120 minutes.
# 9. Nancy at Fisherman's Wharf: 1:00PM to 5:00PM becomes [240, 480] minutes,
#    and min meeting duration is 90 minutes.
# 10. Elizabeth at Richmond District: 9:30AM to 6:30PM becomes [30, 570] minutes,
#    and min meeting duration is 30 minutes.
#
friends = [
    {"name": "Helen",     "location": "Union Square",       "avail_start": 120, "avail_end": 330, "duration": 45},
    {"name": "Sandra",    "location": "Sunset District",      "avail_start": 645, "avail_end": 735, "duration": 90},
    {"name": "Joseph",    "location": "Nob Hill",           "avail_start": 660, "avail_end": 735, "duration": 75},
    {"name": "Jason",     "location": "Bayview",            "avail_start": 315, "avail_end": 600, "duration": 90},
    {"name": "Sarah",     "location": "Financial District", "avail_start": 330, "avail_end": 600, "duration": 90},
    {"name": "Robert",    "location": "Haight-Ashbury",     "avail_start": 60,  "avail_end": 420, "duration": 105},
    {"name": "Carol",     "location": "Pacific Heights",    "avail_start": 345, "avail_end": 705, "duration": 75},
    {"name": "Michelle",  "location": "Golden Gate Park",   "avail_start": 345, "avail_end": 540, "duration": 120},
    {"name": "Nancy",     "location": "Fisherman's Wharf",  "avail_start": 240, "avail_end": 480, "duration": 90},
    {"name": "Elizabeth", "location": "Richmond District",  "avail_start": 30,  "avail_end": 570, "duration": 30},
]

# ---------------------------------------------------------------------
# List of locations – includes all meeting places plus the starting point.
locations = [
    "Mission District",
    "Union Square",
    "Sunset District",
    "Nob Hill",
    "Bayview",
    "Financial District",
    "Haight-Ashbury",
    "Pacific Heights",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Richmond District",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes).
# The keys are tuples (origin, destination).
travel = {
    # From Mission District:
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Richmond District"): 20,

    # From Union Square:
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Richmond District"): 20,

    # From Sunset District:
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Richmond District"): 12,

    # From Nob Hill:
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Richmond District"): 14,

    # From Bayview:
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Richmond District"): 25,

    # From Financial District:
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Nob Hill"): 8,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Richmond District"): 21,

    # From Haight-Ashbury:
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Richmond District"): 10,

    # From Pacific Heights:
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Richmond District"): 12,

    # From Golden Gate Park:
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Richmond District"): 7,

    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Richmond District"): 18,

    # From Richmond District:
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Fisherman's Wharf"): 18,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model
# ---------------------------------------------------------------------
# We use Optimize to maximize the number of meetings scheduled.
opt = Optimize()

num_friends = len(friends)

# Decision variables:
#   x[i] is a Boolean variable indicating if meeting with friend i is scheduled.
#   start[i] is an integer variable representing the meeting’s start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location is Mission District (at time 0).
starting_location = "Mission District"
arrival_time = 0

# For each friend that is scheduled, add constraints:
# (a) the meeting does not start before the friend’s available start,
# (b) the meeting (start time + duration) must finish by the friend’s available end,
# (c) you cannot start meeting until you have enough time to travel from the starting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(starting_location, loc)
    
    opt.add(Implies(x[i], start[i] >= avail_start))
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Non-overlap constraints:
# For every pair of scheduled meetings, enforce that one meeting plus travel time
# finishes before the other meeting starts.
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

# Objective: maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ---------------------------------------------------------------------
# Solve and print the schedule
# ---------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if model.evaluate(x[i]):
            t = model.evaluate(start[i]).as_long()
            schedule.append((t, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            total = 9 * 60 + minutes
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")