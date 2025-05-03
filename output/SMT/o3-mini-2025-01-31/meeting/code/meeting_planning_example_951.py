from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between the various San Francisco locations.
# The travel times are directional.
travel = {
    # From Presidio:
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "The Castro"): 21,
    
    # From Pacific Heights:
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "The Castro"): 16,
    
    # From Golden Gate Park:
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "The Castro"): 13,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "The Castro"): 27,
    
    # From Mission District:
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "The Castro"): 7,
    
    # From North Beach:
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "The Castro"): 23,
    
    # From Embarcadero:
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "The Castro"): 25,
    
    # From Nob Hill:
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "The Castro"): 17,
    
    # From Chinatown:
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "The Castro"): 22,
    
    # From Sunset District:
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "The Castro"): 17,
    
    # From The Castro:
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Sunset District"): 17,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Initialize the Z3 optimization model.
opt = Optimize()

# You arrive at Presidio at 9:00AM. Time is measured (in minutes) relative to 9:00AM.
arrival_location = "Presidio"
arrival_time = 0

# Friend meeting constraints.
# Times are in minutes after 9:00AM.
# Margaret: at Pacific Heights from 1:30PM to 6:45PM.
#   1:30PM: 13:30 - 9:00 = 270 minutes.
#   6:45PM: 18:45 - 9:00 = 585 minutes.
#   Required duration: 30 minutes.
# Daniel: at Golden Gate Park from 11:15AM to 12:15PM.
#   11:15AM: 135 minutes; 12:15PM: 195 minutes; duration: 15 minutes.
# William: at Fisherman's Wharf from 11:15AM to 5:15PM.
#   11:15AM: 135 minutes; 5:15PM: 525 minutes; duration: 60 minutes.
# George: at Mission District from 9:00PM to 10:00PM.
#   9:00PM: 720 minutes; 10:00PM: 780 minutes; duration: 30 minutes.
# Deborah: at North Beach from 11:00AM to 8:15PM.
#   11:00AM: 120 minutes; 8:15PM: 20:15 - 9:00 = 675 minutes; duration: 120 minutes.
# Betty: at Embarcadero from 4:15PM to 6:00PM.
#   4:15PM: 435 minutes; 6:00PM: 540 minutes; duration: 60 minutes.
# Steven: at Nob Hill from 8:30PM to 9:45PM.
#   8:30PM: 690 minutes; 9:45PM: 765 minutes; duration: 60 minutes.
# Linda: at Chinatown from 8:15PM to 10:00PM.
#   8:15PM: 675 minutes; 10:00PM: 780 minutes; duration: 105 minutes.
# Nancy: at Sunset District from 7:45AM to 5:30PM.
#   7:45AM: 7:45 - 9:00 = -75 minutes; 5:30PM: 17:30 - 9:00 = 510 minutes; duration: 60 minutes.
# Lisa: at The Castro from 9:00PM to 9:45PM.
#   9:00PM: 720 minutes; 9:45PM: 765 minutes; duration: 15 minutes.
friends = [
    {"name": "Margaret", "location": "Pacific Heights", "avail_start": 270, "avail_end": 585, "duration": 30},
    {"name": "Daniel",   "location": "Golden Gate Park", "avail_start": 135, "avail_end": 195, "duration": 15},
    {"name": "William",  "location": "Fisherman's Wharf", "avail_start": 135, "avail_end": 525, "duration": 60},
    {"name": "George",   "location": "Mission District", "avail_start": 720, "avail_end": 780, "duration": 30},
    {"name": "Deborah",  "location": "North Beach", "avail_start": 120, "avail_end": 675, "duration": 120},
    {"name": "Betty",    "location": "Embarcadero", "avail_start": 435, "avail_end": 540, "duration": 60},
    {"name": "Steven",   "location": "Nob Hill", "avail_start": 690, "avail_end": 765, "duration": 60},
    {"name": "Linda",    "location": "Chinatown", "avail_start": 675, "avail_end": 780, "duration": 105},
    {"name": "Nancy",    "location": "Sunset District", "avail_start": -75, "avail_end": 510, "duration": 60},
    {"name": "Lisa",     "location": "The Castro", "avail_start": 720, "avail_end": 765, "duration": 15},
]

num_friends = len(friends)

# Define all relevant locations.
locations = [
    "Presidio",
    "Pacific Heights",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Mission District",
    "North Beach",
    "Embarcadero",
    "Nob Hill",
    "Chinatown",
    "Sunset District",
    "The Castro",
]

# Decision variables:
# For each friend i, define:
#   x[i] - a Boolean variable indicating if the meeting is scheduled.
#   start[i] - an integer variable for the start time (in minutes after 9:00AM) of the meeting.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# For every scheduled meeting, enforce that:
# 1. The meeting does not start before the friend is available.
# 2. The meeting (start time plus required duration) finishes by the friend’s available end.
# 3. There is enough time to travel from your arrival location (Presidio) to the friend’s location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# For every pair of scheduled meetings i and j, ensure that they do not overlap.
# That is, either meeting i (plus its duration and travel time from i's location to j's location)
# is finished before meeting j starts, or vice-versa.
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

# Set objective: maximize the number of meetings scheduled.
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
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")