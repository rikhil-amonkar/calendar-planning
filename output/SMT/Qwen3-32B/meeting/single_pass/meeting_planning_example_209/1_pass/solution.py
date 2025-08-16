from z3 import *
import itertools
import json

# Define friends and their data
friends_data = {
    'Melissa': {
        'location': 'North Beach',
        'available_start': 495,  # 8:15 AM
        'available_end': 810,    # 1:30 PM
        'required': 105
    },
    'Anthony': {
        'location': 'Chinatown',
        'available_start': 795,  # 1:15 PM
        'available_end': 870,    # 2:30 PM
        'required': 60
    },
    'Rebecca': {
        'location': 'Russian Hill',
        'available_start': 1170, # 7:30 PM
        'available_end': 1275,   # 9:15 PM
        'required': 105
    }
}

# Travel times
travel_time = {
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4,
}

friends_list = ['Melissa', 'Anthony', 'Rebecca']

# Function to convert minutes to HH:MM
def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Try all permutations
for perm in itertools.permutations(friends_list):
    # Create variables for each friend's start time
    var_dict = {}
    for friend in perm:
        var_dict[friend] = Int(friend + '_start')
    
    solver = Solver()
    
    # Initial current time and location
    current_time = 540  # 9:00 AM
    current_location = 'Sunset District'
    
    # Track variables for each friend
    for i, friend in enumerate(perm):
        # Get friend's data
        f_data = friends_data[friend]
        loc = f_data['location']
        available_start = f_data['available_start']
        available_end = f_data['available_end']
        required = f_data['required']
        
        # Travel from current_location to loc
        travel_duration = travel_time[(current_location, loc)]
        arrival_time = current_time + travel_duration
        
        # Get the variable for this friend's start time
        s_var = var_dict[friend]
        
        # Add constraints
        solver.add(s_var >= arrival_time)
        solver.add(s_var >= available_start)
        solver.add(s_var + required <= available_end)
        
        # Update current_time and current_location
        current_time = s_var + required
        current_location = loc
    
    # Check if this permutation is feasible
    if solver.check() == sat:
        model = solver.model()
        # Extract the start times
        schedule = []
        for friend in perm:
            s_val = model.eval(var_dict[friend]).as_long()
            end_val = s_val + friends_data[friend]['required']
            schedule.append({
                'action': 'meet',
                'person': friend,
                'start_time': minutes_to_time(s_val),
                'end_time': minutes_to_time(end_val)
            })
        # Output the solution
        print("SOLUTION:")
        print(json.dumps({"itinerary": schedule}))
        exit()