from z3 import *

# Define friends data
friends = [
    {
        'name': 'Daniel',
        'district': 2,  # Nob Hill
        'earliest': 8*60 + 15,  # 8:15 AM
        'latest': 11*60,        # 11:00 AM
        'duration': 15
    },
    {
        'name': 'Elizabeth',
        'district': 3,  # Presidio
        'earliest': 21*60 + 15, # 9:15 PM
        'latest': 22*60 + 15,   # 10:15 PM
        'duration': 45
    },
    {
        'name': 'Steven',
        'district': 4,  # Marina District
        'earliest': 16*60 + 30,  # 4:30 PM
        'latest': 20*60 + 45,   # 8:45 PM
        'duration': 90
    },
    {
        'name': 'Timothy',
        'district': 5,  # Pacific Heights
        'earliest': 12*60,  # 12:00 PM
        'latest': 18*60,   # 6:00 PM
        'duration': 90
    },
    {
        'name': 'Kevin',
        'district': 7,  # Chinatown
        'earliest': 12*60,  # 12:00 PM
        'latest': 19*60,   # 7:00 PM
        'duration': 30
    },
    {
        'name': 'Betty',
        'district': 8,  # Richmond District
        'earliest': 13*60 + 15,  # 1:15 PM
        'latest': 15*60 + 45,    # 3:45 PM
        'duration': 30
    },
    {
        'name': 'Lisa',
        'district': 1,  # The Castro
        'earliest': 19*60 + 15, # 7:15 PM
        'latest': 21*60 + 15,   # 9:15 PM
        'duration': 120
    },
    {
        'name': 'Ashley',
        'district': 6,  # Golden Gate Park
        'earliest': 20*60 + 45, # 8:45 PM
        'latest': 21*60 + 45,   # 9:45 PM
        'duration': 60
    },
]

# Define travel times between districts
travel_times = [
    [0, 7, 12, 25, 19, 16, 17, 16, 20],  # Mission (0)
    [7, 0, 16, 20, 21, 16, 11, 22, 16],   # The Castro (1)
    [13, 17, 0, 17, 11, 8, 17, 6, 14],    # Nob Hill (2)
    [26, 21, 18, 0, 11, 11, 12, 21, 7],   # Presidio (3)
    [20, 22, 12, 10, 0, 7, 18, 15, 11],   # Marina (4)
    [15, 16, 8, 11, 6, 0, 15, 11, 12],    # Pacific Heights (5)
    [17, 13, 20, 11, 16, 16, 0, 23, 7],   # Golden Gate Park (6)
    [17, 22, 9, 19, 12, 10, 23, 0, 20],   # Chinatown (7)
    [20, 16, 17, 7, 9, 10, 9, 20, 0]      # Richmond (8)
]

# Number of steps (max friends to consider)
num_steps = 8

# Create Z3 variables
persons = [Int('person_%d' % i) for i in range(num_steps)]
starts = [Int('start_%d' % i) for i in range(num_steps)]
ends = [Int('end_%d' % i) for i in range(num_steps)]

prev_ends = [Int('prev_end_%d' % i) for i in range(num_steps + 1)]
prev_districts = [Int('prev_district_%d' % i) for i in range(num_steps + 1)]

solver = Optimize()

# Initial state: start at Mission District at 9:00 AM (540 minutes)
solver.add(prev_ends[0] == 9*60)
solver.add(prev_districts[0] == 0)  # Mission District

# For each step
for i in range(num_steps):
    # Generate current_district_expr based on persons[i]
    current_district_expr = 0  # default if person is 0
    for p in range(1, 9):
        friend_index = p - 1
        district = friends[friend_index]['district']
        current_district_expr = If(persons[i] == p, district, current_district_expr)
    
    # Generate travel_time_expr
    travel_time_expr = travel_times[prev_districts[i]][current_district_expr]
    
    # Generate earliest_expr
    earliest_expr = 0
    for p in range(1, 9):
        friend_index = p - 1
        earliest = friends[friend_index]['earliest']
        earliest_expr = If(persons[i] == p, earliest, earliest_expr)
    
    # Generate latest_expr
    latest_expr = 0
    for p in range(1, 9):
        friend_index = p - 1
        latest = friends[friend_index]['latest']
        latest_expr = If(persons[i] == p, latest, latest_expr)
    
    # Generate duration_expr
    duration_expr = 0
    for p in range(1, 9):
        friend_index = p - 1
        duration = friends[friend_index]['duration']
        duration_expr = If(persons[i] == p, duration, duration_expr)
    
    # Add constraints for this step
    solver.add(Implies(persons[i] != 0, starts[i] >= prev_ends[i] + travel_time_expr))
    solver.add(Implies(persons[i] != 0, starts[i] >= earliest_expr))
    solver.add(Implies(persons[i] != 0, ends[i] == starts[i] + duration_expr))
    solver.add(Implies(persons[i] != 0, ends[i] <= latest_expr))
    
    # Update prev_end and prev_district for next step
    solver.add(prev_ends[i+1] == If(persons[i] != 0, ends[i], prev_ends[i]))
    solver.add(prev_districts[i+1] == If(persons[i] != 0, current_district_expr, prev_districts[i]))

# Ensure no duplicate friends
for i in range(num_steps):
    for j in range(i+1, num_steps):
        solver.add(Or(persons[i] == 0, persons[j] == 0, persons[i] != persons[j]))

# Maximize the number of friends met
total_friends = Sum([If(persons[i] != 0, 1, 0) for i in range(num_steps)])
solver.maximize(total_friends)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Extract the itinerary
    itinerary = []
    for i in range(num_steps):
        person_val = model.eval(persons[i])
        if person_val != 0:
            p = person_val.as_long()
            friend_index = p - 1
            start_val = model.eval(starts[i]).as_long()
            end_val = model.eval(ends[i]).as_long()
            name = friends[friend_index]['name']
            start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })
    
    # Print the result
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")