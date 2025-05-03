from z3 import *

# -----------------------------------------------------------------------------
# Travel distances (in minutes) between locations.
# The keys are tuples (origin, destination)
travel = {
    # From Alamo Square
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    
    # From Haight-Ashbury
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    
    # From Union Square
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    
    # From Embarcadero
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Pacific Heights"): 11,
    
    # From North Beach
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Pacific Heights"): 8,
    
    # From Fisherman's Wharf
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    
    # From Presidio
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Pacific Heights"): 11,
    
    # From Financial District
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Pacific Heights"): 13,
    
    # From Chinatown
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    
    # From Mission District
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Financial District"): 15,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Pacific Heights"): 16,
    
    # From Pacific Heights
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
}

def get_travel_time(origin, destination):
    return travel[(origin, destination)]

# -----------------------------------------------------------------------------
# Create the Z3 optimizer.
opt = Optimize()

# You arrive at Alamo Square at 9:00AM.
arrival_location = "Alamo Square"
arrival_time = 0  # minutes after 9:00AM

# Friend meeting data.
# Times are expressed in minutes after 9:00AM. (Negative values indicate times before 9:00AM.)
# Sarah: at Haight-Ashbury from 3:30PM to 10:00PM -> [390, 780], duration: 15 minutes.
# Amanda: at Union Square from 5:15PM to 5:45PM -> [495, 525], duration: 30 minutes.
# Robert: at Embarcadero from 1:30PM to 2:45PM -> [270, 345], duration: 45 minutes.
# Jeffrey: at North Beach from 7:30PM to 8:45PM -> [630, 705], duration: 75 minutes.
# Timothy: at Fisherman's Wharf from 2:00PM to 8:00PM -> [300, 660], duration: 45 minutes.
# Charles: at Presidio from 2:45PM to 7:15PM -> [345, 615], duration: 120 minutes.
# Ashley: at Financial District from 8:15AM to 11:00AM -> [ -45, 120 ], duration: 120 minutes.
# Mary: at Chinatown from 9:45AM to 12:00PM -> [45, 180], duration: 120 minutes.
# Kimberly: at Mission District from 6:30PM to 8:15PM -> [570, 675], duration: 105 minutes.
# Karen: at Pacific Heights from 4:15PM to 8:45PM -> [435, 705], duration: 105 minutes.
friends = [
    {"name": "Sarah",    "location": "Haight-Ashbury",    "avail_start": 390, "avail_end": 780, "duration": 15},
    {"name": "Amanda",   "location": "Union Square",      "avail_start": 495, "avail_end": 525, "duration": 30},
    {"name": "Robert",   "location": "Embarcadero",       "avail_start": 270, "avail_end": 345, "duration": 45},
    {"name": "Jeffrey",  "location": "North Beach",       "avail_start": 630, "avail_end": 705, "duration": 75},
    {"name": "Timothy",  "location": "Fisherman's Wharf", "avail_start": 300, "avail_end": 660, "duration": 45},
    {"name": "Charles",  "location": "Presidio",          "avail_start": 345, "avail_end": 615, "duration": 120},
    {"name": "Ashley",   "location": "Financial District","avail_start": -45, "avail_end": 120, "duration": 120},
    {"name": "Mary",     "location": "Chinatown",         "avail_start": 45,  "avail_end": 180, "duration": 120},
    {"name": "Kimberly", "location": "Mission District",  "avail_start": 570, "avail_end": 675, "duration": 105},
    {"name": "Karen",    "location": "Pacific Heights",   "avail_start": 435, "avail_end": 705, "duration": 105},
]

num_friends = len(friends)

# All locations in the problem.
locations = [
    "Alamo Square", "Haight-Ashbury", "Union Square", "Embarcadero",
    "North Beach", "Fisherman's Wharf", "Presidio", "Financial District",
    "Chinatown", "Mission District", "Pacific Heights",
]

# Decision variables:
# For each friend, x[i] is a Boolean that indicates whether the meeting is scheduled.
# start[i] is an integer representing the start time (in minutes after 9:00AM) of the meeting.
x = [Bool(f"x_{i}") for i in range(num_friends)]
start = [Int(f"start_{i}") for i in range(num_friends)]
for i in range(num_friends):
    # Allow start times in a sufficiently large interval.
    opt.add(start[i] >= -300, start[i] <= 1000)

# For every meeting that is scheduled, enforce:
# 1. The meeting start is no earlier than the friend's available start.
# 2. The meeting ends (start + duration) no later than the friend's available end.
# 3. You can travel from your arrival location (Alamo Square) to the meeting location.
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
# For any two meetings that are scheduled, require that one meeting's end time plus the
# travel time to the second meeting's location is no later than the start time of that meeting.
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

# Objective: Maximize the total number of meetings scheduled.
opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

# -----------------------------------------------------------------------------
# Solve the scheduling problem and output the itinerary.
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