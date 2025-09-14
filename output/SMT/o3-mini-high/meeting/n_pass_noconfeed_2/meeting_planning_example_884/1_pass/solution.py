from z3 import Optimize, Int, Bool, If, And, Implies, sat
import json

# Travel times in minutes as provided. Keys are (from, to).
travel_times = {
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,
    
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 20,
    
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,
    
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,
    
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,
    
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 25,
    
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Bayview"): 21,
    
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Bayview"): 23,
    
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Golden Gate Park"): 22
}

# Friend meeting data
# Times are in minutes from midnight.
# Robert: 7:45=465, 17:30=1050, min_duration 120
# David: 12:30=750, 19:45=1185, min_duration 45
# Matthew: 8:45=525, 13:45=825, min_duration 90
# Jessica: 9:30=570, 18:45=1125, min_duration 45
# Melissa: 7:15=435, 16:45=1005, min_duration 45
# Mark: 15:15=915, 17:00=1020, min_duration 45
# Deborah: 19:00=1140, 19:45=1185, min_duration 45
# Karen: 19:30=1170, 22:00=1320, min_duration 120
# Laura: 21:15=1275, 22:15=1335, min_duration 15
friends = [
    {"name": "Robert", "location": "Chinatown", "avail_start": 465, "avail_end": 1050, "min_duration": 120},
    {"name": "David", "location": "Sunset District", "avail_start": 750, "avail_end": 1185, "min_duration": 45},
    {"name": "Matthew", "location": "Alamo Square", "avail_start": 525, "avail_end": 825, "min_duration": 90},
    {"name": "Jessica", "location": "Financial District", "avail_start": 570, "avail_end": 1125, "min_duration": 45},
    {"name": "Melissa", "location": "North Beach", "avail_start": 435, "avail_end": 1005, "min_duration": 45},
    {"name": "Mark", "location": "Embarcadero", "avail_start": 915, "avail_end": 1020, "min_duration": 45},
    {"name": "Deborah", "location": "Presidio", "avail_start": 1140, "avail_end": 1185, "min_duration": 45},
    {"name": "Karen", "location": "Golden Gate Park", "avail_start": 1170, "avail_end": 1320, "min_duration": 120},
    {"name": "Laura", "location": "Bayview", "avail_start": 1275, "avail_end": 1335, "min_duration": 15}
]

num_friends = len(friends)
# Starting location and time (in minutes from midnight)
start_location = "Richmond District"
start_time = 540  # 9:00 AM

# Create an Optimize object
opt = Optimize()

# Decision variables for each friend:
#   scheduled[i]: whether we plan to meet friend i.
#   s[i]: meeting start time (in minutes).
#   e[i]: meeting end time.
#   pos[i]: position/order in the itinerary (0 if not scheduled, otherwise between 1 and num_friends)
scheduled = [Bool(f"scheduled_{i}") for i in range(num_friends)]
s_vars = [Int(f"s_{i}") for i in range(num_friends)]
e_vars = [Int(f"e_{i}") for i in range(num_friends)]
pos_vars = [Int(f"pos_{i}") for i in range(num_friends)]

# Add domain constraints for meeting times and ordering positions.
for i in range(num_friends):
    # meeting time must be within a day
    opt.add(s_vars[i] >= 0, s_vars[i] <= 1440)
    opt.add(e_vars[i] >= 0, e_vars[i] <= 1440)
    # if scheduled then meeting times and durations respect availability and minimum duration.
    friend = friends[i]
    opt.add(If(scheduled[i],
               And(s_vars[i] >= friend["avail_start"],
                   e_vars[i] <= friend["avail_end"],
                   e_vars[i] - s_vars[i] >= friend["min_duration"]),
               True))
    # enforce that if scheduled then pos in [1, num_friends] else pos == 0
    opt.add(If(scheduled[i],
               And(pos_vars[i] >= 1, pos_vars[i] <= num_friends),
               pos_vars[i] == 0))

# Uniqueness of positions among scheduled meetings.
for i in range(num_friends):
    for j in range(i+1, num_friends):
        opt.add(Implies(And(scheduled[i], scheduled[j]), pos_vars[i] != pos_vars[j]))

# Chain constraints: For a friend in the first position, account for travel from the starting location.
for i in range(num_friends):
    friend = friends[i]
    travel_from_start = travel_times.get((start_location, friend["location"]), 9999)
    opt.add(Implies(And(scheduled[i], pos_vars[i] == 1),
                    s_vars[i] >= start_time + travel_from_start))

# For every pair of friends, if one immediately follows the other in the itinerary, enforce travel constraint.
for i in range(num_friends):
    for j in range(num_friends):
        if i == j:
            continue
        # if friend i immediately precedes friend j (i.e. pos_j = pos_i + 1)
        travel_ij = travel_times.get((friends[i]["location"], friends[j]["location"]), 9999)
        opt.add(Implies(And(scheduled[i], scheduled[j], pos_vars[j] == pos_vars[i] + 1),
                        s_vars[j] >= e_vars[i] + travel_ij))

# Objective: maximize the number of meetings scheduled.
objective = sum([If(scheduled[i], 1, 0) for i in range(num_friends)])
h = opt.maximize(objective)

# Check and get model
if opt.check() == sat:
    model = opt.model()
    
    # Collect scheduled meetings with their positions, start and end times.
    itinerary = []
    # Build a list of tuples: (position, friend data, start, end)
    scheduled_meetings = []
    for i in range(num_friends):
        if model.evaluate(scheduled[i]):
            pos_val = model.evaluate(pos_vars[i])
            s_val = model.evaluate(s_vars[i])
            e_val = model.evaluate(e_vars[i])
            # Convert Z3 numbers to Python int
            try:
                pos_int = int(pos_val.as_long())
                s_int = int(s_val.as_long())
                e_int = int(e_val.as_long())
            except:
                pos_int = int(pos_val)
                s_int = int(s_val)
                e_int = int(e_val)
            scheduled_meetings.append((pos_int, friends[i], s_int, e_int))
    
    # Sort meetings by their scheduled order (position)
    scheduled_meetings.sort(key=lambda x: x[0])
    
    def minutes_to_time(m):
        hour = m // 60
        minute = m % 60
        return f"{hour}:{minute:02d}"
    
    for pos_val, friend, s_int, e_int in scheduled_meetings:
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(s_int),
            "end_time": minutes_to_time(e_int)
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))