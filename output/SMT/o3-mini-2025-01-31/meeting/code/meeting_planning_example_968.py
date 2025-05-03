from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# Each key is a tuple (origin, destination)
travel = {
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Union Square"): 19,
    
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Union Square"): 22,
    
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Union Square"): 9,
    
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Union Square"): 18,
    
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Union Square"): 13,
    
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Union Square"): 10,
    
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Union Square"): 21,
    
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Union Square"): 30,
    
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Union Square"): 7,
    
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
    
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at The Castro at 9:00 AM.
arrival_location = "The Castro"
arrival_time = 0  # minutes after 9:00 AM

# Friend meeting data.
# Times are expressed in minutes after 9:00 AM. (Negative values indicate before 9:00 AM.)
# For example, Kevin’s available window from 8:45AM to 11:00AM becomes:
# 8:45AM = -15 (9:00AM - 15min) and 11:00AM = 120.
friends = [
    # Kevin: at Golden Gate Park from 8:45AM to 11:00AM, meeting ≥15 minutes.
    {"name": "Kevin", "location": "Golden Gate Park", "avail_start": -15, "avail_end": 120, "duration": 15},
    # Charles: at Financial District from 4:15PM to 9:15PM (435 to 735), meeting ≥120 minutes.
    {"name": "Charles", "location": "Financial District", "avail_start": 435, "avail_end": 735, "duration": 120},
    # Ronald: at Bayview from 7:15AM to 8:45AM (-105 to -15), meeting ≥90 minutes.
    {"name": "Ronald", "location": "Bayview", "avail_start": -105, "avail_end": -15, "duration": 90},
    # Jason: at Fisherman's Wharf from 3:45PM to 9:00PM (405 to 720), meeting ≥75 minutes.
    {"name": "Jason", "location": "Fisherman's Wharf", "avail_start": 405, "avail_end": 720, "duration": 75},
    # Kenneth: at Russian Hill from 2:15PM to 3:30PM (315 to 390), meeting ≥45 minutes.
    {"name": "Kenneth", "location": "Russian Hill", "avail_start": 315, "avail_end": 390, "duration": 45},
    # Laura: at Richmond District from 7:00AM to 9:15PM (-120 to 735), meeting ≥75 minutes.
    {"name": "Laura", "location": "Richmond District", "avail_start": -120, "avail_end": 735, "duration": 75},
    # Joshua: at Sunset District from 1:00PM to 7:30PM (240 to 630), meeting ≥45 minutes.
    {"name": "Joshua", "location": "Sunset District", "avail_start": 240, "avail_end": 630, "duration": 45},
    # Michelle: at North Beach from 8:15PM to 9:00PM (675 to 720), meeting ≥45 minutes.
    {"name": "Michelle", "location": "North Beach", "avail_start": 675, "avail_end": 720, "duration": 45},
    # Amanda: at Alamo Square from 3:15PM to 7:30PM (375 to 630), meeting ≥90 minutes.
    {"name": "Amanda", "location": "Alamo Square", "avail_start": 375, "avail_end": 630, "duration": 90},
    # Emily: at Union Square from 7:15AM to 12:30PM (-105 to 210), meeting ≥105 minutes.
    {"name": "Emily", "location": "Union Square", "avail_start": -105, "avail_end": 210, "duration": 105},
]

num_friends = len(friends)

# List of neighborhoods used in the problem.
locations = [
    "The Castro", "Golden Gate Park", "Financial District", "Bayview",
    "Fisherman's Wharf", "Russian Hill", "Richmond District", "Sunset District",
    "North Beach", "Alamo Square", "Union Square"
]

# Decision variables:
# For each friend, x[i] indicates if the meeting is scheduled.
# start[i] is the meeting’s start time (in minutes after 9:00 AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # A sufficiently large time window.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For each scheduled meeting, enforce:
# 1. The meeting starts no earlier than the friend’s available start.
# 2. The meeting ends (start + duration) by the friend’s available end.
# 3. There is enough travel time from the arrival location (The Castro) to the meeting location.
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
# For any two scheduled meetings, one must finish (plus travel time between the two locations)
# before the other starts.
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

# Objective: maximize the total number of meetings.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve and output the itinerary.
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