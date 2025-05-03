from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times are measured in minutes after 9:00AM at Golden Gate Park (time = 0).

# Deborah: at Marina District from 8:00AM to 3:00PM.
#   8:00AM = -60 minutes; 3:00PM = 360 minutes.
#   Minimum meeting duration: 15 minutes.
# Elizabeth: at Sunset District from 7:45PM to 9:45PM.
#   7:45PM = 645 minutes; 9:45PM = 765 minutes.
#   Minimum meeting duration: 60 minutes.
# David: at Richmond District from 9:30AM to 4:45PM.
#   9:30AM = 30 minutes; 4:45PM = 465 minutes.
#   Minimum meeting duration: 105 minutes.
# Patricia: at Chinatown from 5:00PM to 8:00PM.
#   5:00PM = 480 minutes; 8:00PM = 660 minutes.
#   Minimum meeting duration: 120 minutes.
# Jeffrey: at Financial District from 9:45PM to 10:45PM.
#   9:45PM = 765 minutes; 10:45PM = 825 minutes.
#   Minimum meeting duration: 60 minutes.
# Charles: at Fisherman's Wharf from 3:00PM to 10:00PM.
#   3:00PM = 360 minutes; 10:00PM = 780 minutes.
#   Minimum meeting duration: 120 minutes.
# Andrew: at Haight-Ashbury from 9:45PM to 10:45PM.
#   9:45PM = 765 minutes; 10:45PM = 825 minutes.
#   Minimum meeting duration: 45 minutes.
# Michelle: at Embarcadero from 6:30PM to 8:45PM.
#   6:30PM = 570 minutes; 8:45PM = 705 minutes.
#   Minimum meeting duration: 90 minutes.
# Thomas: at Russian Hill from 1:15PM to 10:00PM.
#   1:15PM = 255 minutes; 10:00PM = 780 minutes.
#   Minimum meeting duration: 90 minutes.
# Brian: at Presidio from 8:15PM to 9:30PM.
#   8:15PM = 675 minutes; 9:30PM = 750 minutes.
#   Minimum meeting duration: 75 minutes.

friends = [
    {"name": "Deborah",   "location": "Marina District",    "avail_start": -60,  "avail_end": 360, "duration": 15},
    {"name": "Elizabeth", "location": "Sunset District",      "avail_start": 645,  "avail_end": 765, "duration": 60},
    {"name": "David",     "location": "Richmond District",    "avail_start": 30,   "avail_end": 465, "duration": 105},
    {"name": "Patricia",  "location": "Chinatown",          "avail_start": 480,  "avail_end": 660, "duration": 120},
    {"name": "Jeffrey",   "location": "Financial District",   "avail_start": 765,  "avail_end": 825, "duration": 60},
    {"name": "Charles",   "location": "Fisherman's Wharf",    "avail_start": 360,  "avail_end": 780, "duration": 120},
    {"name": "Andrew",    "location": "Haight-Ashbury",       "avail_start": 765,  "avail_end": 825, "duration": 45},
    {"name": "Michelle",  "location": "Embarcadero",          "avail_start": 570,  "avail_end": 705, "duration": 90},
    {"name": "Thomas",    "location": "Russian Hill",         "avail_start": 255,  "avail_end": 780, "duration": 90},
    {"name": "Brian",     "location": "Presidio",             "avail_start": 675,  "avail_end": 750, "duration": 75},
]

# -----------------------------------------------------------------------------
# List of locations.
# Our arrival is at Golden Gate Park at 9:00AM.
locations = [
    "Golden Gate Park",   # Arrival location at 9:00AM.
    "Marina District",
    "Sunset District",
    "Richmond District",
    "Chinatown",
    "Financial District",
    "Fisherman's Wharf",
    "Haight-Ashbury",
    "Embarcadero",
    "Russian Hill",
    "Presidio",
]

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From Golden Gate Park:
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    
    # From Marina District:
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Presidio"): 10,
    
    # From Sunset District:
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    
    # From Richmond District:
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Presidio"): 7,
    
    # From Chinatown:
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    
    # From Financial District:
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Presidio"): 22,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Presidio"): 17,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Presidio"): 15,
    
    # From Embarcadero:
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Presidio"): 20,
    
    # From Russian Hill:
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Presidio"): 14,
    
    # From Presidio:
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Russian Hill"): 14,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 model, constraints, and optimization.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# For each friend i:
#   x[i] indicates whether we schedule a meeting with friend i.
#   start[i] is an integer representing the meeting start time (in minutes after 9:00AM at Golden Gate Park).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# Our arrival is at Golden Gate Park at time = 0.
arrival_location = "Golden Gate Park"
arrival_time = 0

# For each scheduled friend, enforce:
#  - Meeting starts no earlier than the friend’s available start.
#  - Meeting ends (start + duration) no later than the friend’s available end.
#  - There is enough travel time from our arrival (Golden Gate Park) to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Pairwise non-overlap constraints:
# For any two scheduled meetings, require that either meeting i (plus its duration and travel time to j’s location)
# finishes before meeting j starts, or vice versa.
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

# Objective: maximize the number of meetings scheduled.
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
    # Sort schedule by start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Golden Gate Park):")
    
    def format_time(m):
        # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) into HH:MM.
        total = 540 + m
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")