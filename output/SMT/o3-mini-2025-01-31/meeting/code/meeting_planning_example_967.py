from z3 import *

# ---------------------------------------------------------------------------
# Travel times (in minutes) between locations.
# Keys are (origin, destination)
travel = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Nob Hill"): 7,
    
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Nob Hill"): 8,
    
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Nob Hill"): 15,
    
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Nob Hill"): 20,
    
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Nob Hill"): 12,
    
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "Nob Hill"): 12,
    
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Nob Hill"): 27,
    
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Nob Hill"): 9,
    
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Nob Hill"): 20,
    
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Golden Gate Park"): 17,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# ---------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at North Beach at 9:00 AM (time 0 in minutes after 9:00 AM).
arrival_location = "North Beach"
arrival_time = 0

# Friend meeting data.
# Times are expressed in minutes after 9:00 AM.
# Convert times as follows:
# For example, a meeting starting at 4:45PM is 16:45 which is 16*60+45=1005 minutes after midnight, 
# minus 540 (minutes for 9:00AM) equals 465.
friends = [
    # Timothy: at Pacific Heights from 4:45PM (465) to 6:30PM (570), duration: 15 minutes.
    {"name": "Timothy", "location": "Pacific Heights", "avail_start": 465, "avail_end": 570, "duration": 15},
    # James: at Haight-Ashbury from 10:30AM (90) to 11:15AM (135), duration: 30 minutes.
    {"name": "James", "location": "Haight-Ashbury", "avail_start": 90, "avail_end": 135, "duration": 30},
    # Mark: at Fisherman's Wharf from 4:00PM (420) to 10:00PM (780), duration: 15 minutes.
    {"name": "Mark", "location": "Fisherman's Wharf", "avail_start": 420, "avail_end": 780, "duration": 15},
    # Barbara: at Bayview from 7:45AM (-75) to 9:45AM (45), duration: 30 minutes.
    {"name": "Barbara", "location": "Bayview", "avail_start": -75, "avail_end": 45, "duration": 30},
    # Lisa: at Mission District from 12:00PM (180) to 1:30PM (270), duration: 30 minutes.
    {"name": "Lisa", "location": "Mission District", "avail_start": 180, "avail_end": 270, "duration": 30},
    # Brian: at Marina District from 8:15PM (675) to 10:00PM (780), duration: 105 minutes.
    {"name": "Brian", "location": "Marina District", "avail_start": 675, "avail_end": 780, "duration": 105},
    # Linda: at Sunset District from 5:00PM (480) to 7:15PM (615), duration: 105 minutes.
    {"name": "Linda", "location": "Sunset District", "avail_start": 480, "avail_end": 615, "duration": 105},
    # Daniel: at Chinatown from 3:15PM (375) to 5:45PM (525), duration: 120 minutes.
    {"name": "Daniel", "location": "Chinatown", "avail_start": 375, "avail_end": 525, "duration": 120},
    # Mary: at Golden Gate Park from 7:30AM (-90) to 8:00PM (660), duration: 90 minutes.
    {"name": "Mary", "location": "Golden Gate Park", "avail_start": -90, "avail_end": 660, "duration": 90},
    # Sandra: at Nob Hill from 10:15AM (75) to 9:15PM (735), duration: 105 minutes.
    {"name": "Sandra", "location": "Nob Hill", "avail_start": 75, "avail_end": 735, "duration": 105},
]

num_friends = len(friends)

# List of locations used in the problem.
locations = [
    "North Beach", "Pacific Heights", "Haight-Ashbury", "Fisherman's Wharf", "Bayview",
    "Mission District", "Marina District", "Sunset District", "Chinatown", "Golden Gate Park", "Nob Hill"
]

# Decision variables:
# For each friend, x[i] indicates whether the meeting is scheduled.
# start[i] represents the meeting start time (in minutes after 9:00 AM).
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow start times in a generous range.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For every scheduled meeting, we enforce:
# 1. The meeting must not start before the friend’s available start time.
# 2. The meeting must finish (start + duration) by the friend’s available end time.
# 3. You must have enough time to travel from your arrival location (North Beach) to the meeting location.
for i, friend in enumerate(friends):
    dur = friend["duration"]
    a_start = friend["avail_start"]
    a_end = friend["avail_end"]
    loc = friend["location"]
    # Travel time from your starting point (North Beach) to the friend’s location.
    travel_from_arrival = get_travel_time(arrival_location, loc)
    
    opt.add(Implies(x[i], start[i] >= a_start))
    opt.add(Implies(x[i], start[i] + dur <= a_end))
    opt.add(Implies(x[i], start[i] >= arrival_time + get_travel_time(arrival_location, loc)))

# Non-overlap constraints:
# For any two meetings that are scheduled, one must finish (plus travel time) before the next starts.
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

# Objective: Maximize the number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# ----------------------------------------------------------------------------
# Solve the scheduling problem and output the itinerary.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for i in range(num_friends):
        if is_true(model.evaluate(x[i])):
            s_time = model.evaluate(start[i]).as_long()
            schedule.append((s_time, friends[i]["name"], friends[i]["location"], friends[i]["duration"]))
    schedule.sort(key=lambda tup: tup[0])
    
    print("Optimal Schedule (times are minutes after 9:00 AM):")
    def format_time(minutes_after9):
        # 9:00 AM is 540 minutes after midnight.
        total = 540 + minutes_after9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    for s_time, name, loc, dur in schedule:
        finish = s_time + dur
        print(f"Meet {name} at {loc} from {format_time(s_time)} to {format_time(finish)} (duration {dur} mins)")
else:
    print("No feasible schedule found.")