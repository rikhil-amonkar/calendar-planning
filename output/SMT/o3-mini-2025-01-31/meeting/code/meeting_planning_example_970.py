from z3 import *

# -------------------------------------------------------------------------
# Travel times between neighborhoods (in minutes; directional)
travel = {
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "North Beach"): 19,

    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,

    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "North Beach"): 9,

    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "North Beach"): 7,

    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "North Beach"): 5,

    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "North Beach"): 17,

    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "North Beach"): 18,

    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "North Beach"): 11,

    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "North Beach"): 17,

    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "North Beach"): 28,

    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Sunset District"): 27,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at Haight-Ashbury at 9:00AM.
arrival_location = "Haight-Ashbury"
arrival_time = 0  # minutes after 9:00 AM

# Friend meeting data.
# Times are expressed in minutes relative to 9:00AM (negative values indicate before 9:00AM).
friends = [
    # Ronald: at Fisherman's Wharf from 7:45PM to 9:30PM, meeting ≥60 minutes.
    {"name": "Ronald", "location": "Fisherman's Wharf", "avail_start": 645, "avail_end": 750, "duration": 60},
    # Jessica: at Pacific Heights from 7:00AM to 6:00PM, meeting ≥15 minutes.
    {"name": "Jessica", "location": "Pacific Heights", "avail_start": -120, "avail_end": 540, "duration": 15},
    # Steven: at Financial District from 3:15PM to 7:30PM, meeting ≥60 minutes.
    {"name": "Steven", "location": "Financial District", "avail_start": 375, "avail_end": 630, "duration": 60},
    # Paul: at Russian Hill from 7:45AM to 5:30PM, meeting ≥45 minutes.
    {"name": "Paul", "location": "Russian Hill", "avail_start": -75, "avail_end": 510, "duration": 45},
    # Andrew: at Mission District from 6:00PM to 9:45PM, meeting ≥45 minutes.
    {"name": "Andrew", "location": "Mission District", "avail_start": 540, "avail_end": 765, "duration": 45},
    # Carol: at Presidio from 12:15PM to 4:30PM, meeting ≥60 minutes.
    {"name": "Carol", "location": "Presidio", "avail_start": 195, "avail_end": 450, "duration": 60},
    # Joshua: at Marina District from 3:00PM to 7:45PM, meeting ≥75 minutes.
    {"name": "Joshua", "location": "Marina District", "avail_start": 360, "avail_end": 645, "duration": 75},
    # Joseph: at Richmond District from 3:15PM to 6:45PM, meeting ≥45 minutes.
    {"name": "Joseph", "location": "Richmond District", "avail_start": 375, "avail_end": 585, "duration": 45},
    # Betty: at Sunset District from 5:30PM to 9:45PM, meeting ≥120 minutes.
    {"name": "Betty", "location": "Sunset District", "avail_start": 510, "avail_end": 765, "duration": 120},
    # Stephanie: at North Beach from 6:30PM to 9:30PM, meeting ≥120 minutes.
    {"name": "Stephanie", "location": "North Beach", "avail_start": 570, "avail_end": 750, "duration": 120},
]

num_friends = len(friends)

# List of relevant locations.
locations = ["Haight-Ashbury", "Fisherman's Wharf", "Pacific Heights", "Financial District",
             "Russian Hill", "Mission District", "Presidio", "Marina District",
             "Richmond District", "Sunset District", "North Beach"]

# Decision variables:
# For each friend, x[i] is a Boolean indicating if we schedule that meeting.
# start[i] is the meeting's start time (in minutes after 9:00AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # restrict start time to a reasonable range.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, add constraints:
# (a) meeting starts no earlier than the friend’s available start.
# (b) meeting ends (start + duration) by the friend’s available end.
# (c) meeting start is not before the earliest arrival time at that location (from Haight-Ashbury).
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
# For any two meetings that are both selected, ensure that either one finishes (plus travel time) before the other starts.
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

# -------------------------------------------------------------------------
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
        # 9:00 AM is 540 minutes after midnight.
        total = 540 + minutes_after_9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")