from z3 import *

# Define friends
friends = [
    {
        'name': 'Betty',
        'location': 'Russian Hill',
        'available_start': 420,  # 7:00 AM
        'available_end': 1005,   # 4:45 PM
        'required_duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'Alamo Square',
        'available_start': 570,  # 9:30 AM
        'available_end': 1035,   # 5:15 PM
        'required_duration': 105
    },
    {
        'name': 'Joshua',
        'location': 'Haight-Ashbury',
        'available_start': 735,  # 12:15 PM
        'available_end': 1320,   # 7:00 PM
        'required_duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Marina District',
        'available_start': 735,  # 12:15 PM
        'available_end': 1380,   # 6:00 PM
        'required_duration': 45
    },
    {
        'name': 'James',
        'location': 'Bayview',
        'available_start': 450,  # 7:30 AM
        'available_end': 1680,   # 8:00 PM
        'required_duration': 90
    },
    {
        'name': 'Anthony',
        'location': 'Chinatown',
        'available_start': 705,  # 11:45 AM
        'available_end': 750,    # 1:30 PM
        'required_duration': 75
    },
    {
        'name': 'Timothy',
        'location': 'Presidio',
        'available_start': 750,  # 12:30 PM
        'available_end': 825,    # 2:45 PM
        'required_duration': 90
    },
    {
        'name': 'Emily',
        'location': 'Sunset District',
        'available_start': 1170, # 7:30 PM
        'available_end': 1230,   # 9:30 PM
        'required_duration': 120
    }
]

# Define travel times between locations
travel_times = {
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Sunset District'): 16,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Sunset District'): 19,
    ('Bayview', 'Union Square'): 18,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Sunset District'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'Bayview'): 20,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Sunset District'): 29,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 16,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Presidio'): 16,
}

# Create solver
solver = Optimize()

# Create variables for each friend
for friend in friends:
    friend['include'] = Bool(f"include_{friend['name']}")
    friend['start'] = Int(f"start_{friend['name']}")
    friend['end'] = Int(f"end_{friend['name']}")
    friend['position'] = Int(f"position_{friend['name']}")

# Add constraints for each friend
for friend in friends:
    include = friend['include']
    start = friend['start']
    end = friend['end']
    position = friend['position']
    available_start = friend['available_start']
    available_end = friend['available_end']
    required_duration = friend['required_duration']
    location = friend['location']
    
    # If included, start >= available_start
    solver.add(Implies(include, start >= available_start))
    
    # If included, end <= available_end
    solver.add(Implies(include, end <= available_end))
    
    # If included, duration is sufficient
    solver.add(Implies(include, end - start >= required_duration))
    
    # If included and position is 0, start >= 540 + travel time from Union Square to location
    travel_time_union_to_loc = travel_times.get(('Union Square', location), 0)
    solver.add(Implies(And(include, position == 0), start >= 540 + travel_time_union_to_loc))
    
    # Also, if included, position >= 0
    solver.add(Implies(include, position >= 0))

# Add pairwise constraints between friends
for i, friendA in enumerate(friends):
    for j, friendB in enumerate(friends):
        if i == j:
            continue
        includeA = friendA['include']
        includeB = friendB['include']
        positionA = friendA['position']
        positionB = friendB['position']
        startA = friendA['start']
        endA = friendA['end']
        startB = friendB['start']
        endB = friendB['end']
        locationA = friendA['location']
        locationB = friendB['location']
        
        # If both included, positions must be different
        solver.add(Implies(And(includeA, includeB), positionA != positionB))
        
        # If A is before B, then startB >= endA + travel time from A to B
        travel_time_A_to_B = travel_times.get((locationA, locationB), 0)
        solver.add(Implies(And(includeA, includeB, positionA < positionB), startB >= endA + travel_time_A_to_B))
        
        # If B is before A, then startA >= endB + travel time from B to A
        travel_time_B_to_A = travel_times.get((locationB, locationA), 0)
        solver.add(Implies(And(includeA, includeB, positionB < positionA), startA >= endB + travel_time_B_to_A))

# Objective: maximize the number of included friends
obj_expr = Sum([If(friend['include'], 1, 0) for friend in friends])
solver.maximize(obj_expr)

# Check for satisfiability
result = solver.check()
if result == sat:
    model = solver.model()
    # Extract the included friends and their times
    included_friends = []
    for friend in friends:
        if is_true(model.eval(friend['include'])):
            start_time = model.eval(friend['start']).as_long()
            end_time = model.eval(friend['end']).as_long()
            # Convert minutes to HH:MM
            start_h = start_time // 60
            start_m = start_time % 60
            end_h = end_time // 60
            end_m = end_time % 60
            included_friends.append({
                'person': friend['name'],
                'start_time': f"{start_h:02d}:{start_m:02d}",
                'end_time': f"{end_h:02d}:{end_m:02d}"
            })
    # Sort included friends by start time to form the itinerary
    included_friends.sort(key=lambda x: int(x['start_time'].replace(':', '')))
    # Output the solution
    solution = {
        "itinerary": included_friends
    }
    print(solution)
else:
    print("No solution found.")