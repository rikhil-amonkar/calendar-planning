from z3 import *

# -----------------------------------------------------------------------------
# Travel distances between locations (in minutes)
travel = {
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Sunset District"): 24,
    
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Sunset District"): 23,
    
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Sunset District"): 17,
    
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Sunset District"): 19,
    
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Sunset District"): 27,
    
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Sunset District"): 15,
    
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Sunset District"): 11,
    
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Sunset District"): 15,
    
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Sunset District"): 10,
    
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Alamo Square"): 17,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at Nob Hill at 9:00AM.
arrival_location = "Nob Hill"
arrival_time = 0  # minutes after 9:00 AM

# Friend meeting data.
# Times are expressed in minutes after 9:00AM.
# (Negative times indicate times before 9:00AM.)
friends = [
    # Charles: at Russian Hill from 7:30AM to 10:00AM, meeting ≥45 minutes.
    {"name": "Charles", "location": "Russian Hill", "avail_start": -90, "avail_end": 60, "duration": 45},
    # Joseph: at The Castro from 2:30PM to 7:45PM, meeting ≥120 minutes.
    {"name": "Joseph", "location": "The Castro", "avail_start": 330, "avail_end": 645, "duration": 120},
    # Emily: at Marina District from 10:15AM to 10:00PM, meeting ≥75 minutes.
    {"name": "Emily", "location": "Marina District", "avail_start": 75, "avail_end": 780, "duration": 75},
    # Sandra: at Fisherman's Wharf from 8:15PM to 10:00PM, meeting ≥105 minutes.
    {"name": "Sandra", "location": "Fisherman's Wharf", "avail_start": 675, "avail_end": 780, "duration": 105},
    # Steven: at Haight-Ashbury from 12:45PM to 8:00PM, meeting ≥90 minutes.
    {"name": "Steven", "location": "Haight-Ashbury", "avail_start": 225, "avail_end": 660, "duration": 90},
    # Michelle: at Richmond District from 2:45PM to 7:15PM, meeting ≥15 minutes.
    {"name": "Michelle", "location": "Richmond District", "avail_start": 345, "avail_end": 615, "duration": 15},
    # Carol: at Presidio from 8:45AM to 10:45AM, meeting ≥90 minutes.
    {"name": "Carol", "location": "Presidio", "avail_start": -15, "avail_end": 105, "duration": 90},
    # Deborah: at Golden Gate Park from 12:00PM to 5:00PM, meeting ≥75 minutes.
    {"name": "Deborah", "location": "Golden Gate Park", "avail_start": 180, "avail_end": 480, "duration": 75},
    # Helen: at Alamo Square from 12:15PM to 3:00PM, meeting ≥105 minutes.
    {"name": "Helen", "location": "Alamo Square", "avail_start": 195, "avail_end": 360, "duration": 105},
    # Linda: at Sunset District from 10:00AM to 7:45PM, meeting ≥30 minutes.
    {"name": "Linda", "location": "Sunset District", "avail_start": 60, "avail_end": 645, "duration": 30},
]

num_friends = len(friends)

# List of locations in our problem.
locations = ["Nob Hill", "Russian Hill", "The Castro", "Marina District",
             "Fisherman's Wharf", "Haight-Ashbury", "Richmond District", "Presidio",
             "Golden Gate Park", "Alamo Square", "Sunset District"]

# Decision variables:
# For each friend, a Boolean x[i] indicates whether we schedule that meeting.
# start[i] represents the meeting’s start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, enforce:
# (1) the meeting starts no earlier than the friend’s available start,
# (2) the meeting ends (start[i] + duration) by the friend’s available end,
# (3) there is enough travel time from the arrival location (for the first meeting).
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    travel_from_arrival = get_travel_time(arrival_location, loc)
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Non-overlap constraints:
# For any two meetings that are both scheduled, ensure that either i comes entirely before j (with travel time)
# or j comes entirely before i.
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

# Objective: maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve and print the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00 AM):")
    def format_time(minutes_after_9):
        total = 540 + minutes_after_9  # 9:00 AM is 540 minutes after midnight.
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")