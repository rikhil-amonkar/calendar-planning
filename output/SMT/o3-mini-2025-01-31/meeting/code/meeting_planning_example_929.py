from z3 import *

# -----------------------------------------------------------------------------
# Friend definitions.
# Times (in minutes after 9:00AM at Marina District):
# Matthew: at Alamo Square, available 2:15PM to 5:30PM --> [315, 510], duration >= 45
# Kenneth: at Nob Hill, available 5:15PM to 7:30PM --> [495, 630], duration >= 90
# Elizabeth: at Presidio, available 10:30AM to 9:45PM --> [90, 765], duration >= 90
# Emily: at North Beach, available 7:15PM to 8:15PM --> [615, 675], duration >= 60
# George: at Fisherman's Wharf, available 9:30AM to 3:15PM --> [30, 375], duration >= 105
# Laura: at Russian Hill, available 11:00AM to 3:15PM --> [120, 375], duration >= 30
# John: at Haight-Ashbury, available 2:15PM to 5:00PM --> [315, 480], duration >= 120
# Joseph: at Bayview, available 7:15PM to 8:45PM --> [615, 705], duration >= 90
# Kevin: at Mission District, available 4:30PM to 5:30PM --> [450, 510], duration >= 60
# Charles: at Richmond District, available 1:00PM to 9:00PM --> [240, 720], duration >= 75
friends = [
    {"name": "Matthew",   "location": "Alamo Square",      "avail_start": 315, "avail_end": 510, "duration": 45},
    {"name": "Kenneth",   "location": "Nob Hill",          "avail_start": 495, "avail_end": 630, "duration": 90},
    {"name": "Elizabeth", "location": "Presidio",          "avail_start": 90,  "avail_end": 765, "duration": 90},
    {"name": "Emily",     "location": "North Beach",       "avail_start": 615, "avail_end": 675, "duration": 60},
    {"name": "George",    "location": "Fisherman's Wharf", "avail_start": 30,  "avail_end": 375, "duration": 105},
    {"name": "Laura",     "location": "Russian Hill",      "avail_start": 120, "avail_end": 375, "duration": 30},
    {"name": "John",      "location": "Haight-Ashbury",    "avail_start": 315, "avail_end": 480, "duration": 120},
    {"name": "Joseph",    "location": "Bayview",           "avail_start": 615, "avail_end": 705, "duration": 90},
    {"name": "Kevin",     "location": "Mission District",  "avail_start": 450, "avail_end": 510, "duration": 60},
    {"name": "Charles",   "location": "Richmond District", "avail_start": 240, "avail_end": 720, "duration": 75},
]

# -----------------------------------------------------------------------------
# List of locations.
locations = [
    "Marina District",
    "Alamo Square",
    "Nob Hill",
    "Presidio",
    "North Beach",
    "Fisherman's Wharf",
    "Russian Hill",
    "Haight-Ashbury",
    "Bayview",
    "Mission District",
    "Richmond District",
]

# -----------------------------------------------------------------------------
# Travel distances between locations (in minutes).
travel = {
    # From Marina District:
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Richmond District"): 11,
    
    # From Alamo Square:
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Richmond District"): 11,
    
    # From Nob Hill:
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Richmond District"): 14,
    
    # From Presidio:
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Richmond District"): 7,
    
    # From North Beach:
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Richmond District"): 18,
    
    # From Fisherman's Wharf:
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 23,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Richmond District"): 18,
    
    # From Russian Hill:
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Richmond District"): 14,
    
    # From Haight-Ashbury:
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Richmond District"): 10,
    
    # From Bayview:
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Richmond District"): 25,
    
    # From Mission District:
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Richmond District"): 20,
    
    # From Richmond District:
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Mission District"): 20,
}

# Helper function to obtain travel time between two locations.
def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Z3 Model and Optimization.
# -----------------------------------------------------------------------------
# We use Optimize() to maximize the total number of meetings scheduled.
opt = Optimize()
num_friends = len(friends)

# Decision variables:
# x[i]: a Boolean variable indicating whether to schedule a meeting with friend i.
# start[i]: an integer variable for the meeting start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]

# Allow start times to be in a wide range.
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# You arrive at Marina District at 9:00AM (time = 0).
arrival_location = "Marina District"
arrival_time = 0

# For each scheduled meeting, enforce its time window and that you can reach the location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end   = friend["avail_end"]
    loc     = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    # Meeting must start no earlier than the friend’s availability,
    # finish by the available end, and start after you can get there.
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + travel_from_arrival))

# Add pairwise non-overlap constraints.
# For any two scheduled meetings, ensure that one finishes (plus travel time to the next location)
# before the other starts.
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
# Solve and print the optimal itinerary.
# -----------------------------------------------------------------------------
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00AM at Marina District):")
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        def to_time(m):
            # Convert minutes after 9:00AM (9:00AM = 540 minutes after midnight) to HH:MM.
            total = 540 + m
            hour = total // 60
            minute = total % 60
            return f"{hour:02d}:{minute:02d}"
        print(f"Meet {name} at {loc} from {to_time(s_time)} to {to_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")