import z3
import json

# Define friends and their data
friends = [
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'available_start': 10 * 60 + 30,  # 10:30 AM
        'available_end': 20 * 60,         # 8:00 PM
        'min_duration': 90
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'available_start': 15 * 60 + 15,  # 3:15 PM
        'available_end': 19 * 60,         # 7:00 PM
        'min_duration': 45
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'available_start': 7 * 60,        # 7:00 AM
        'available_end': 20 * 60,         # 8:00 PM
        'min_duration': 120
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': 19 * 60 + 30,  # 7:30 PM
        'available_end': 19 * 60 + 30 + 30,  # 8:30 PM
        'min_duration': 30
    },
    {
        'name': 'Robert',
        'location': "Fisherman's Wharf",
        'available_start': 10 * 60,       # 10:00 AM
        'available_end': 15 * 60,         # 3:00 PM
        'min_duration': 15
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'available_start': 10 * 60 + 45,  # 10:45 AM
        'available_end': 13 * 60,         # 1:00 PM
        'min_duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'available_start': 18 * 60 + 15,  # 6:15 PM
        'available_end': 20 * 60,         # 8:00 PM
        'min_duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'Sunset District',
        'available_start': 10 * 60 + 15,  # 10:15 AM
        'available_end': 18 * 60 + 15,    # 6:15 PM
        'min_duration': 105
    },
    {
        'name': 'Amanda',
        'location': 'Golden Gate Park',
        'available_start': 7 * 60 + 45,   # 7:45 AM
        'available_end': 18 * 60 + 45,    # 6:45 PM
        'min_duration': 15
    }
]

# Parse travel times
location_names = [
    'Haight-Ashbury',
    'Mission District',
    'Union Square',
    'Pacific Heights',
    'Bayview',
    "Fisherman's Wharf",
    'Marina District',
    'Richmond District',
    'Sunset District',
    'Golden Gate Park'
]

# Travel data
travel_data = [
    ('Haight-Ashbury', 'Mission District', 11),
    ('Haight-Ashbury', 'Union Square', 19),
    ('Haight-Ashbury', 'Pacific Heights', 12),
    ('Haight-Ashbury', 'Bayview', 18),
    ('Haight-Ashbury', "Fisherman's Wharf", 23),
    ('Haight-Ashbury', 'Marina District', 17),
    ('Haight-Ashbury', 'Richmond District', 10),
    ('Haight-Ashbury', 'Sunset District', 15),
    ('Haight-Ashbury', 'Golden Gate Park', 7),
    ('Mission District', 'Haight-Ashbury', 12),
    ('Mission District', 'Union Square', 15),
    ('Mission District', 'Pacific Heights', 16),
    ('Mission District', 'Bayview', 14),
    ('Mission District', "Fisherman's Wharf", 22),
    ('Mission District', 'Marina District', 19),
    ('Mission District', 'Richmond District', 20),
    ('Mission District', 'Sunset District', 24),
    ('Mission District', 'Golden Gate Park', 17),
    ('Union Square', 'Haight-Ashbury', 18),
    ('Union Square', 'Mission District', 14),
    ('Union Square', 'Pacific Heights', 15),
    ('Union Square', 'Bayview', 15),
    ('Union Square', "Fisherman's Wharf", 15),
    ('Union Square', 'Marina District', 18),
    ('Union Square', 'Richmond District', 20),
    ('Union Square', 'Sunset District', 27),
    ('Union Square', 'Golden Gate Park', 22),
    ('Pacific Heights', 'Haight-Ashbury', 11),
    ('Pacific Heights', 'Mission District', 15),
    ('Pacific Heights', 'Union Square', 12),
    ('Pacific Heights', 'Bayview', 22),
    ('Pacific Heights', "Fisherman's Wharf", 13),
    ('Pacific Heights', 'Marina District', 6),
    ('Pacific Heights', 'Richmond District', 12),
    ('Pacific Heights', 'Sunset District', 21),
    ('Pacific Heights', 'Golden Gate Park', 15),
    ('Bayview', 'Haight-Ashbury', 19),
    ('Bayview', 'Mission District', 13),
    ('Bayview', 'Union Square', 18),
    ('Bayview', 'Pacific Heights', 23),
    ('Bayview', "Fisherman's Wharf", 25),
    ('Bayview', 'Marina District', 27),
    ('Bayview', 'Richmond District', 25),
    ('Bayview', 'Sunset District', 23),
    ('Bayview', 'Golden Gate Park', 22),
    ("Fisherman's Wharf", 'Haight-Ashbury', 22),
    ("Fisherman's Wharf", 'Mission District', 22),
    ("Fisherman's Wharf", 'Union Square', 13),
    ("Fisherman's Wharf", 'Pacific Heights', 12),
    ("Fisherman's Wharf", 'Bayview', 26),
    ("Fisherman's Wharf", 'Marina District', 9),
    ("Fisherman's Wharf", 'Richmond District', 18),
    ("Fisherman's Wharf", 'Sunset District', 27),
    ("Fisherman's Wharf", 'Golden Gate Park', 25),
    ('Marina District', 'Haight-Ashbury', 16),
    ('Marina District', 'Mission District', 20),
    ('Marina District', 'Union Square', 16),
    ('Marina District', 'Pacific Heights', 7),
    ('Marina District', 'Bayview', 27),
    ('Marina District', "Fisherman's Wharf", 10),
    ('Marina District', 'Richmond District', 11),
    ('Marina District', 'Sunset District', 19),
    ('Marina District', 'Golden Gate Park', 18),
    ('Richmond District', 'Haight-Ashbury', 10),
    ('Richmond District', 'Mission District', 20),
    ('Richmond District', 'Union Square', 21),
    ('Richmond District', 'Pacific Heights', 10),
    ('Richmond District', 'Bayview', 27),
    ('Richmond District', "Fisherman's Wharf", 18),
    ('Richmond District', 'Marina District', 9),
    ('Richmond District', 'Sunset District', 11),
    ('Richmond District', 'Golden Gate Park', 9),
    ('Sunset District', 'Haight-Ashbury', 15),
    ('Sunset District', 'Mission District', 25),
    ('Sunset District', 'Union Square', 30),
    ('Sunset District', 'Pacific Heights', 21),
    ('Sunset District', 'Bayview', 22),
    ('Sunset District', "Fisherman's Wharf", 29),
    ('Sunset District', 'Marina District', 21),
    ('Sunset District', 'Richmond District', 12),
    ('Sunset District', 'Golden Gate Park', 11),
    ('Golden Gate Park', 'Haight-Ashbury', 7),
    ('Golden Gate Park', 'Mission District', 17),
    ('Golden Gate Park', 'Union Square', 22),
    ('Golden Gate Park', 'Pacific Heights', 16),
    ('Golden Gate Park', 'Bayview', 23),
    ('Golden Gate Park', "Fisherman's Wharf", 24),
    ('Golden Gate Park', 'Marina District', 16),
    ('Golden Gate Park', 'Richmond District', 7),
    ('Golden Gate Park', 'Sunset District', 10),
]

# Create travel_time_matrix
num_locations = len(location_names)
travel_time_matrix = [[0]*num_locations for _ in range(num_locations)]
for from_loc, to_loc, time in travel_data:
    from_idx = location_names.index(from_loc)
    to_idx = location_names.index(to_loc)
    travel_time_matrix[from_idx][to_idx] = time

# Precompute location indices for each friend
loc_indices = []
for friend in friends:
    loc = friend['location']
    idx = location_names.index(loc)
    loc_indices.append(idx)

# Create Z3 solver
s = z3.Optimize()

# Create variables
include = []
order = []
start_time = []
end_time = []

for i in range(len(friends)):
    include.append(z3.Bool(f'include_{i}'))
    order.append(z3.Int(f'order_{i}'))
    start_time.append(z3.Int(f'start_{i}'))
    end_time.append(z3.Int(f'end_{i}'))

# Add constraints for each friend
for i in range(len(friends)):
    # If included, start and end times must satisfy availability and duration
    s.add(z3.Implies(include[i], start_time[i] >= friends[i]['available_start']))
    s.add(z3.Implies(include[i], end_time[i] <= friends[i]['available_end']))
    s.add(z3.Implies(include[i], end_time[i] == start_time[i] + friends[i]['min_duration']))

    # If included and order is 0, start time must be >= arrival time at location
    loc_i = loc_indices[i]
    s.add(z3.Implies(z3.And(include[i], order[i] == 0), start_time[i] >= 9 * 60 + travel_time_matrix[0][loc_i]))

# Add constraints for consecutive friends
for i in range(len(friends)):
    for j in range(len(friends)):
        if i != j:
            loc_i = loc_indices[i]
            loc_j = loc_indices[j]
            travel_time = travel_time_matrix[loc_j][loc_i]
            # If include_i and include_j and order_i == order_j + 1, then start_time_i >= end_time_j + travel_time
            constraint = z3.Implies(
                z3.And(include[i], include[j], order[i] == order[j] + 1),
                start_time[i] >= end_time[j] + travel_time
            )
            s.add(constraint)

# Ensure unique orders for included friends
for i in range(len(friends)):
    for j in range(i+1, len(friends)):
        s.add(z3.Implies(z3.And(include[i], include[j]), order[i] != order[j]))

# Maximize the number of included friends
s.maximize(z3.Sum([z3.If(include[i], 1, 0) for i in range(len(friends))]))

# Check for a solution
if s.check() == z3.sat:
    model = s.model()
    result = []
    for i in range(len(friends)):
        if model.evaluate(include[i]):
            # Get order, start, end times
            ord_val = model.evaluate(order[i])
            start_val = model.evaluate(start_time[i])
            end_val = model.evaluate(end_time[i])
            # Convert times to H:MM format
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            result.append({
                "action": "meet",
                "location": friends[i]['location'],
                "person": friends[i]['name'],
                "start_time": to_time_str(start_val.as_long()),
                "end_time": to_time_str(end_val.as_long())
            })
    # Sort the result by order
    sorted_result = []
    for i in range(len(friends)):
        if model.evaluate(include[i]):
            ord_val = model.evaluate(order[i]).as_long()
            sorted_result.append((ord_val, {
                "action": "meet",
                "location": friends[i]['location'],
                "person": friends[i]['name'],
                "start_time": to_time_str(model.evaluate(start_time[i]).as_long()),
                "end_time": to_time_str(model.evaluate(end_time[i]).as_long())
            }))
    sorted_result.sort()
    itinerary = [item[1] for item in sorted_result]
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}))