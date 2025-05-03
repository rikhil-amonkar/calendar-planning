from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each entry is directional.
travel = {
    # From The Castro:
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Marina District"): 21,
    
    # From Presidio:
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Marina District"): 11,
    
    # From Richmond District:
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Marina District"): 9,
    
    # From Embarcadero:
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "Marina District"): 12,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Marina District"): 9,
    
    # From Nob Hill:
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Marina District"): 11,
    
    # From Mission District:
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Marina District"): 19,
    
    # From Pacific Heights:
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Marina District"): 6,
    
    # From North Beach:
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Marina District"): 9,
    
    # From Union Square:
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Marina District"): 18,
    
    # From Marina District:
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Embarcadero"): 14,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Union Square"): 16,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Define the Z3 optimization model.
opt = Optimize()

# Our arrival is at The Castro at 9:00AM, so time = 0.
arrival_location = "The Castro"
arrival_time = 0

# Define friend meeting constraints.
# Times are in minutes after 9:00AM.
# Amanda: at Presidio from 3:00PM to 7:15PM -> 3:00PM = 360, 7:15PM = 615, duration = 45.
# Matthew: at Richmond District from 8:15PM to 10:00PM -> 8:15PM = 675, 10:00PM = 780, duration = 105.
# Charles: at Embarcadero from 7:45AM to 10:15AM -> 7:45AM = -75, 10:15AM = 75, duration = 30.
# George: at Fisherman's Wharf from 10:15AM to 11:45AM -> 10:15AM = 75, 11:45AM = 165, duration = 75.
# Robert: at Nob Hill from 11:45AM to 2:30PM -> 11:45AM = 165, 2:30PM = 330, duration = 105.
# Stephanie: at Mission District from 4:00PM to 8:45PM -> 4:00PM = 420, 8:45PM = 705, duration = 120.
# Thomas: at Pacific Heights from 9:15PM to 9:45PM -> 9:15PM = 735, 9:45PM = 765, duration = 30.
# Lisa: at North Beach from 8:00AM to 3:30PM -> 8:00AM = -60, 3:30PM = 390, duration = 105.
# Betty: at Union Square from 4:15PM to 8:30PM -> 4:15PM = 435, 8:30PM = 570, duration = 30.
# Rebecca: at Marina District from 2:30PM to 3:30PM -> 2:30PM = 330, 3:30PM = 390, duration = 30.

friends = [
    {"name": "Amanda",     "location": "Presidio",          "avail_start": 360, "avail_end": 615, "duration": 45},
    {"name": "Matthew",    "location": "Richmond District", "avail_start": 675, "avail_end": 780, "duration": 105},
    {"name": "Charles",    "location": "Embarcadero",       "avail_start": -75, "avail_end": 75,  "duration": 30},
    {"name": "George",     "location": "Fisherman's Wharf", "avail_start": 75,  "avail_end": 165, "duration": 75},
    {"name": "Robert",     "location": "Nob Hill",          "avail_start": 165, "avail_end": 330, "duration": 105},
    {"name": "Stephanie",  "location": "Mission District",  "avail_start": 420, "avail_end": 705, "duration": 120},
    {"name": "Thomas",     "location": "Pacific Heights",   "avail_start": 735, "avail_end": 765, "duration": 30},
    {"name": "Lisa",       "location": "North Beach",       "avail_start": -60, "avail_end": 390, "duration": 105},
    {"name": "Betty",      "location": "Union Square",      "avail_start": 435, "avail_end": 570, "duration": 30},
    {"name": "Rebecca",    "location": "Marina District",   "avail_start": 330, "avail_end": 390, "duration": 30},
]

num_friends = len(friends)

# List of all locations used.
locations = [
    "The Castro",
    "Presidio",
    "Richmond District",
    "Embarcadero",
    "Fisherman's Wharf",
    "Nob Hill",
    "Mission District",
    "Pacific Heights",
    "North Beach",
    "Union Square",
    "Marina District",
]

# Decision variables for each friend:
# x[i] : a Boolean indicating if the meeting with friend i is scheduled.
# start[i] : the start time (in minutes after 9:00AM) for friend i's meeting.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)  # Broad domain

# For every scheduled friend, impose timing constraints:
# - Meeting cannot start before the friend's available start.
# - Meeting must finish (start + duration) by the friend's available end.
# - There must be enough travel time from our arrival (The Castro) to friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For any two scheduled meetings, add non-overlap constraints.
# That is, if meetings i and j are both scheduled then either:
# meeting i (plus its duration and travel time from its location to j’s location)
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
    # Sort the meetings by start time.
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM):")
    
    def format_time(m):
        # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) to HH:MM format.
        total = 540 + m
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")