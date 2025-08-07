from z3 import *
import json

# Define travel times between locations
travel_time_dict = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Union Square": 22,
        "Sunset District": 15,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Alamo Square": 21,
        "Financial District": 11,
        "Union Square": 13,
        "Sunset District": 27,
        "Embarcadero": 8,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Richmond District": 18
    },
    "Alamo Square": {
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Financial District": 17,
        "Union Square": 14,
        "Sunset District": 16,
        "Embarcadero": 16,
        "Golden Gate Park": 9,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Financial District": {
        "Presidio": 22,
        "Fisherman's Wharf": 10,
        "Alamo Square": 17,
        "Union Square": 9,
        "Sunset District": 30,
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Richmond District": 21
    },
    "Union Square": {
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Alamo Square": 15,
        "Financial District": 9,
        "Sunset District": 27,
        "Embarcadero": 11,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Richmond District": 20
    },
    "Sunset District": {
        "Presidio": 16,
        "Fisherman's Wharf": 29,
        "Alamo Square": 17,
        "Financial District": 30,
        "Union Square": 30,
        "Embarcadero": 30,
        "Golden Gate Park": 11,
        "Chinatown": 30,
        "Richmond District": 12
    },
    "Embarcadero": {
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Alamo Square": 19,
        "Financial District": 5,
        "Union Square": 10,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Chinatown": 7,
        "Richmond District": 21
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Fisherman's Wharf": 24,
        "Alamo Square": 9,
        "Financial District": 26,
        "Union Square": 22,
        "Sunset District": 10,
        "Embarcadero": 25,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Presidio": 19,
        "Fisherman's Wharf": 8,
        "Alamo Square": 17,
        "Financial District": 5,
        "Union Square": 7,
        "Sunset District": 29,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Presidio": 7,
        "Fisherman's Wharf": 18,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Sunset District": 11,
        "Embarcadero": 19,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

# Friend data: names, locations, time windows (in minutes from 9:00 AM), and min meeting times
friend_data = [
    {"name": "Jeffrey", "location": "Fisherman's Wharf", "start_avail": 75, "end_avail": 240, "min_time": 90},  # 10:15 AM to 1:00 PM
    {"name": "Ronald", "location": "Alamo Square", "start_avail": 0, "end_avail": 345, "min_time": 120},        # 7:45 AM to 2:45 PM
    {"name": "Jason", "location": "Financial District", "start_avail": 105, "end_avail": 420, "min_time": 105},  # 10:45 AM to 4:00 PM
    {"name": "Melissa", "location": "Union Square", "start_avail": 525, "end_avail": 555, "min_time": 15},      # 5:45 PM to 6:15 PM
    {"name": "Elizabeth", "location": "Sunset District", "start_avail": 345, "end_avail": 510, "min_time": 105}, # 2:45 PM to 5:30 PM
    {"name": "Margaret", "location": "Embarcadero", "start_avail": 255, "end_avail": 600, "min_time": 90},      # 1:15 PM to 7:00 PM
    {"name": "George", "location": "Golden Gate Park", "start_avail": 600, "end_avail": 780, "min_time": 75},    # 7:00 PM to 10:00 PM
    {"name": "Richard", "location": "Chinatown", "start_avail": 30, "end_avail": 720, "min_time": 15},          # 9:30 AM to 9:00 PM
    {"name": "Laura", "location": "Richmond District", "start_avail": 45, "end_avail": 540, "min_time": 60}     # 9:45 AM to 6:00 PM
]

# Travel times from Presidio to each friend's location (in minutes)
travel_from_presidio = [19, 19, 23, 22, 15, 20, 12, 21, 7]  # For Jeffrey, Ronald, Jason, Melissa, Elizabeth, Margaret, George, Richard, Laura

# Precompute travel time matrix between friends
travel_matrix = []
for i in range(9):
    row = []
    loc_i = friend_data[i]['location']
    for j in range(9):
        loc_j = friend_data[j]['location']
        if loc_i == loc_j:
            # Travel time to same location is 0
            row.append(0)
        else:
            row.append(travel_time_dict[loc_i][loc_j])
    travel_matrix.append(row)

# Initialize Z3 solver
s = Optimize()

# Create Z3 variables
meet = [Bool(f'meet_{i}') for i in range(9)]
next_var = [Int(f'next_{i}') for i in range(9)]
sched_times = [Real(f'sched_{i}') for i in range(9)]

# Constraints for next_var: if meeting i is scheduled, next_var[i] must be in [0,9]
for i in range(9):
    s.add(Implies(meet[i], And(next_var[i] >= 0, next_var[i] <= 9)))
    
    # If next_var[i] points to a meeting j (not end), then j must be scheduled and j != i
    for j in range(9):
        s.add(Implies(And(meet[i], next_var[i] == j), meet[j]))
        s.add(Implies(And(meet[i], next_var[i] == j), next_var[i] != i))

# Compute in_degree for each meeting (number of predecessors)
in_degree = []
for i in range(9):
    deg = 0
    for j in range(9):
        deg += If(And(meet[j], next_var[j] == i), 1, 0)
    in_degree.append(deg)

# Exactly one meeting has in_degree 0 (the first meeting)
s.add(Sum([If(And(meet[i], in_degree[i] == 0), 1, 0) for i in range(9)]) == 1)

# For each meeting that is scheduled, in_degree is either 0 or 1
for i in range(9):
    s.add(Implies(meet[i], Or(in_degree[i] == 0, in_degree[i] == 1)))

# Exactly one meeting points to 9 (the end)
s.add(Sum([If(And(meet[i], next_var[i] == 9), 1, 0) for i in range(9)]) == 1)

# Start time constraints
for i in range(9):
    # If meeting i is the first meeting, start time >= travel time from Presidio
    s.add(Implies(And(meet[i], in_degree[i] == 0), 
                  sched_times[i] >= travel_from_presidio[i]))
    
    # For each possible next meeting j
    for j in range(9):
        s.add(Implies(And(meet[i], next_var[i] == j),
                      sched_times[j] >= sched_times[i] + friend_data[i]['min_time'] + travel_matrix[i][j]))
    
    # Meeting must be within availability window
    s.add(Implies(meet[i], 
                  And(sched_times[i] >= friend_data[i]['start_avail'],
                      sched_times[i] + friend_data[i]['min_time'] <= friend_data[i]['end_avail'])))

# Maximize the number of meetings
s.maximize(Sum([If(meet[i], 1, 0) for i in range(9)]))

# Solve the problem
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(9):
        if is_true(m.evaluate(meet[i])):
            start_val = m.evaluate(sched_times[i])
            # Convert Z3 rational to float
            if is_rational_value(start_val):
                start_min = float(start_val.numerator_as_long()) / float(start_val.denominator_as_long())
            elif is_algebraic_value(start_val):
                start_min = start_val.approx(10).as_fraction()
                start_min = float(start_min.numerator) / float(start_min.denominator)
            else:
                start_min = 0.0
            
            end_min = start_min + friend_data[i]['min_time']
            # Convert to time string (from minutes since 9:00 AM)
            total_start_min = 9*60 + start_min
            hours = int(total_start_min // 60)
            minutes = int(total_start_min % 60)
            start_str = f"{hours:02d}:{minutes:02d}"
            
            total_end_min = 9*60 + end_min
            hours_end = int(total_end_min // 60)
            minutes_end = int(total_end_min % 60)
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": friend_data[i]['name'],
                "start_time": start_str,
                "end_time": end_str
            })
    
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))