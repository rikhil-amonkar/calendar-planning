from z3 import *

# ---------------------------------------------------------------------
# Friend definitions.
#
# All times are in minutes relative to 9:00AM (9:00AM = 0).
#
# 1. Nancy at Pacific Heights from 11:00AM to 5:30PM; minimum meeting = 105 minutes.
#    11:00AM -> 660-540 = 120, 5:30PM -> 1050-540 = 510.
# 2. Kenneth at Marina District from 7:00AM to 5:45PM; minimum meeting = 105 minutes.
#    7:00AM  -> 420-540 = -120, 5:45PM -> 1065-540 = 525.
# 3. Michelle at Presidio from 12:45PM to 7:15PM; minimum meeting = 15 minutes.
#    12:45PM -> 765-540 = 225, 7:15PM -> 1155-540 = 615.
# 4. Joseph at Golden Gate Park from 4:30PM to 8:30PM; minimum meeting = 105 minutes.
#    4:30PM -> 990-540 = 450, 8:30PM -> 1230-540 = 690.
# 5. Paul at Richmond District from 7:45PM to 9:45PM; minimum meeting = 120 minutes.
#    7:45PM -> 1185-540 = 645, 9:45PM -> 1305-540 = 765.
# 6. Daniel at Bayview from 10:30AM to 2:30PM; minimum meeting = 60 minutes.
#    10:30AM -> 630-540 = 90, 2:30PM -> 870-540 = 330.
# 7. George at Embarcadero from 7:45PM to 8:45PM; minimum meeting = 60 minutes.
#    7:45PM -> 1185-540 = 645, 8:45PM -> 1305-540 = 765.
# 8. Charles at Chinatown from 5:15PM to 8:30PM; minimum meeting = 120 minutes.
#    5:15PM -> 1035-540 = 495, 8:30PM -> 1230-540 = 690.
# 9. Rebecca at Nob Hill from 4:45PM to 9:00PM; minimum meeting = 45 minutes.
#    4:45PM -> 1005-540 = 465, 9:00PM -> 1260-540 = 720.
# 10. Lisa at Fisherman's Wharf from 9:15AM to 4:30PM; minimum meeting = 30 minutes.
#     9:15AM -> 555-540 = 15, 4:30PM -> 990-540 = 450.
friends = [
    {"name": "Nancy",    "location": "Pacific Heights",  "avail_start": 120, "avail_end": 510, "duration": 105},
    {"name": "Kenneth",  "location": "Marina District",  "avail_start": -120, "avail_end": 525, "duration": 105},
    {"name": "Michelle", "location": "Presidio",         "avail_start": 225, "avail_end": 615, "duration": 15},
    {"name": "Joseph",   "location": "Golden Gate Park", "avail_start": 450, "avail_end": 690, "duration": 105},
    {"name": "Paul",     "location": "Richmond District", "avail_start": 645, "avail_end": 765, "duration": 120},
    {"name": "Daniel",   "location": "Bayview",          "avail_start": 90,  "avail_end": 330, "duration": 60},
    {"name": "George",   "location": "Embarcadero",      "avail_start": 645, "avail_end": 765, "duration": 60},
    {"name": "Charles",  "location": "Chinatown",        "avail_start": 495, "avail_end": 690, "duration": 120},
    {"name": "Rebecca",  "location": "Nob Hill",         "avail_start": 465, "avail_end": 720, "duration": 45},
    {"name": "Lisa",     "location": "Fisherman's Wharf", "avail_start": 15,  "avail_end": 450, "duration": 30},
]

# ---------------------------------------------------------------------
# List of locations.
locations = [
    "Union Square",
    "Pacific Heights",
    "Marina District",
    "Presidio",
    "Golden Gate Park",
    "Richmond District",
    "Bayview",
    "Embarcadero",
    "Chinatown",
    "Nob Hill",
    "Fisherman's Wharf",
]

# ---------------------------------------------------------------------
# Travel distances between locations (in minutes)
travel = {
    # From Union Square:
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    
    # From Pacific Heights:
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    
    # From Marina District:
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Fisherman's Wharf"): 10,
    
    # From Presidio:
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    
    # From Richmond District:
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Fisherman's Wharf"): 18,
    
    # From Bayview:
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Fisherman's Wharf"): 25,
    
    # From Embarcadero:
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    
    # From Chinatown:
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Fisherman's Wharf"): 8,
    
    # From Nob Hill:
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Nob Hill"): 11,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------
# Z3 Model and Optimization.
# ---------------------------------------------------------------------
# We use Optimize to maximize the number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i:
#   x[i] is a Boolean that is True if the meeting is scheduled.
#   start[i] is the meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Set broad bounds for meeting start times.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Starting location: Union Square at 9:00AM (time = 0).
starting_location = "Union Square"
arrival_time = 0

# For each friend meeting that is scheduled, add the following constraints:
for i, friend in enumerate(friends):
    dur = friend["duration"]
    avail_start = friend["avail_start"]
    avail_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_start = get_travel_time(starting_location, loc)
    
    # Meeting should start no earlier than the friend's availability.
    opt.add(Implies(x[i], start[i] >= avail_start))
    # Meeting must finish (start + duration) within the available end.
    opt.add(Implies(x[i], start[i] + dur <= avail_end))
    # There must be enough time to travel from Union Square.
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_start))

# Add pairwise non-overlap constraints (with travel time between meetings):
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
        if model.evaluate(x[i]):
            t = model.evaluate(start[i]).as_long()
            schedule.append((t, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal schedule (times in minutes after 9:00AM):")
    for t, name, loc, dur in schedule:
        finish = t + dur
        def to_time(minutes):
            total = 540 + minutes  # since 9:00AM is 540 minutes after midnight
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(t)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")