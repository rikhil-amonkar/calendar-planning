from z3 import *

# -----------------------------------------------------------------------------
# Define the travel distances (in minutes) between locations.
travel = {
    # From The Castro:
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    
    # From Financial District:
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    
    # From Marina District:
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Embarcadero"): 14,
    
    # From Union Square:
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Embarcadero"): 11,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    
    # From Russian Hill:
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    
    # From Chinatown:
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    
    # From Sunset District:
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    
    # From Richmond District:
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    
    # From North Beach:
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Embarcadero"): 6,
    
    # From Embarcadero:
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "North Beach"): 5,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimizer.
opt = Optimize()

# You arrive at The Castro at 9:00AM.
arrival_location = "The Castro"
arrival_time = 0  # minutes after 9:00AM

# Define the meeting (friend) information.
# Times are measured in minutes relative to 9:00AM.
# Note: For times before 9:00AM the numbers will be negative.
friends = [
    {"name": "Joseph",    "location": "Financial District", "avail_start": 525, "avail_end": 780, "duration": 75},
    {"name": "Patricia",  "location": "Marina District",    "avail_start": 510, "avail_end": 765, "duration": 75},
    {"name": "Amanda",    "location": "Union Square",       "avail_start": 105, "avail_end": 780, "duration": 105},  # 1:45PM = 105 minutes after 9:00AM
    {"name": "Linda",     "location": "Golden Gate Park",   "avail_start": 240, "avail_end": 435, "duration": 75},   # 1:00PM to 4:15PM
    {"name": "William",   "location": "Russian Hill",       "avail_start": -120, "avail_end": 105, "duration": 120},  # 7:00AM to 10:45AM
    {"name": "Sarah",     "location": "Chinatown",          "avail_start": 30,  "avail_end": 420, "duration": 90},   # 9:30AM to 4:00PM
    {"name": "Rebecca",   "location": "Sunset District",    "avail_start": 540, "avail_end": 525+180, "duration": 75},   # 6:00PM (540) to 8:45PM (525+180=705)
    {"name": "Kevin",     "location": "Richmond District",  "avail_start": 555, "avail_end": 585, "duration": 30},   # 6:15PM to 6:45PM
    {"name": "Margaret",  "location": "North Beach",        "avail_start": 375, "avail_end": 480, "duration": 30},   # 3:15PM to 5:00PM
    {"name": "Emily",     "location": "Embarcadero",        "avail_start": 315, "avail_end": 765, "duration": 45},   # 2:15PM to 9:45PM
]

num_friends = len(friends)

# List of all locations.
locations = [
    "The Castro",
    "Financial District",
    "Marina District",
    "Union Square",
    "Golden Gate Park",
    "Russian Hill",
    "Chinatown",
    "Sunset District",
    "Richmond District",
    "North Beach",
    "Embarcadero",
]

# Decision variables:
# For each friend i we introduce:
#   x[i]: Boolean indicating whether meeting friend i is scheduled.
#   start[i]: Integer for the meeting's start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow start times in a wide interval.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting enforce:
# 1. The meeting start time is no earlier than the friend's available start.
# 2. The meeting (start time + duration) ends by the friend's available end.
# 3. The meeting cannot start before you have traveled from your arrival location (The Castro) to the meeting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Impose non-overlap constraints for every pair of scheduled meetings.
# That is, if both meetings i and j are scheduled then either
# meeting i (including its duration and travel time to meeting j) finishes before meeting j starts,
# or vice versa.
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

# Objective: Maximize the number of scheduled meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the scheduling problem and print the optimal itinerary.
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
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")