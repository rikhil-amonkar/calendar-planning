from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the friends and their details (times in hours)
    friends = {
        'Laura': {'location': 'Alamo Square', 'start': 14.5, 'end': 16.25, 'min_duration': 75/60},
        'Brian': {'location': 'Presidio', 'start': 10.25, 'end': 17.0, 'min_duration': 30/60},
        'Karen': {'location': 'Russian Hill', 'start': 18.0, 'end': 20.25, 'min_duration': 90/60},
        'Stephanie': {'location': 'North Beach', 'start': 10.25, 'end': 16.0, 'min_duration': 75/60},
        'Helen': {'location': 'Golden Gate Park', 'start': 11.5, 'end': 21.75, 'min_duration': 120/60},
        'Sandra': {'location': 'Richmond District', 'start': 8.0, 'end': 15.25, 'min_duration': 30/60},
        'Mary': {'location': 'Embarcadero', 'start': 16.75, 'end': 18.75, 'min_duration': 120/60},
        'Deborah': {'location': 'Financial District', 'start': 19.0, 'end': 20.75, 'min_duration': 105/60},
        'Elizabeth': {'location': 'Marina District', 'start': 8.5, 'end': 13.25, 'min_duration': 105/60},
    }

    # Define travel times (in hours)
    travel_times = {
        ('Mission District', 'Alamo Square'): 11/60,
        ('Mission District', 'Presidio'): 25/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Mission District', 'North Beach'): 17/60,
        ('Mission District', 'Golden Gate Park'): 17/60,
        ('Mission District', 'Richmond District'): 20/60,
        ('Mission District', 'Embarcadero'): 19/60,
        ('Mission District', 'Financial District'): 15/60,
        ('Mission District', 'Marina District'): 19/60,
        ('Alamo Square', 'Mission District'): 10/60,
        ('Alamo Square', 'Presidio'): 17/60,
        ('Alamo Square', 'Russian Hill'): 13/60,
        ('Alamo Square', 'North Beach'): 15/60,
        ('Alamo Square', 'Golden Gate Park'): 9/60,
        ('Alamo Square', 'Richmond District'): 11/60,
        ('Alamo Square', 'Embarcadero'): 16/60,
        ('Alamo Square', 'Financial District'): 17/60,
        ('Alamo Square', 'Marina District'): 15/60,
        ('Presidio', 'Mission District'): 26/60,
        ('Presidio', 'Alamo Square'): 19/60,
        ('Presidio', 'Russian Hill'): 14/60,
        ('Presidio', 'North Beach'): 18/60,
        ('Presidio', 'Golden Gate Park'): 12/60,
        ('Presidio', 'Richmond District'): 7/60,
        ('Presidio', 'Embarcadero'): 20/60,
        ('Presidio', 'Financial District'): 23/60,
        ('Presidio', 'Marina District'): 11/60,
        ('Russian Hill', 'Mission District'): 16/60,
        ('Russian Hill', 'Alamo Square'): 15/60,
        ('Russian Hill', 'Presidio'): 14/60,
        ('Russian Hill', 'North Beach'): 5/60,
        ('Russian Hill', 'Golden Gate Park'): 21/60,
        ('Russian Hill', 'Richmond District'): 14/60,
        ('Russian Hill', 'Embarcadero'): 8/60,
        ('Russian Hill', 'Financial District'): 11/60,
        ('Russian Hill', 'Marina District'): 7/60,
        ('North Beach', 'Mission District'): 18/60,
        ('North Beach', 'Alamo Square'): 16/60,
        ('North Beach', 'Presidio'): 17/60,
        ('North Beach', 'Russian Hill'): 4/60,
        ('North Beach', 'Golden Gate Park'): 22/60,
        ('North Beach', 'Richmond District'): 18/60,
        ('North Beach', 'Embarcadero'): 6/60,
        ('North Beach', 'Financial District'): 8/60,
        ('North Beach', 'Marina District'): 9/60,
        ('Golden Gate Park', 'Mission District'): 17/60,
        ('Golden Gate Park', 'Alamo Square'): 9/60,
        ('Golden Gate Park', 'Presidio'): 11/60,
        ('Golden Gate Park', 'Russian Hill'): 19/60,
        ('Golden Gate Park', 'North Beach'): 23/60,
        ('Golden Gate Park', 'Richmond District'): 7/60,
        ('Golden Gate Park', 'Embarcadero'): 25/60,
        ('Golden Gate Park', 'Financial District'): 26/60,
        ('Golden Gate Park', 'Marina District'): 16/60,
        ('Richmond District', 'Mission District'): 20/60,
        ('Richmond District', 'Alamo Square'): 13/60,
        ('Richmond District', 'Presidio'): 7/60,
        ('Richmond District', 'Russian Hill'): 13/60,
        ('Richmond District', 'North Beach'): 17/60,
        ('Richmond District', 'Golden Gate Park'): 9/60,
        ('Richmond District', 'Embarcadero'): 19/60,
        ('Richmond District', 'Financial District'): 22/60,
        ('Richmond District', 'Marina District'): 9/60,
        ('Embarcadero', 'Mission District'): 20/60,
        ('Embarcadero', 'Alamo Square'): 19/60,
        ('Embarcadero', 'Presidio'): 20/60,
        ('Embarcadero', 'Russian Hill'): 8/60,
        ('Embarcadero', 'North Beach'): 5/60,
        ('Embarcadero', 'Golden Gate Park'): 25/60,
        ('Embarcadero', 'Richmond District'): 21/60,
        ('Embarcadero', 'Financial District'): 5/60,
        ('Embarcadero', 'Marina District'): 12/60,
        ('Financial District', 'Mission District'): 17/60,
        ('Financial District', 'Alamo Square'): 17/60,
        ('Financial District', 'Presidio'): 22/60,
        ('Financial District', 'Russian Hill'): 11/60,
        ('Financial District', 'North Beach'): 7/60,
        ('Financial District', 'Golden Gate Park'): 23/60,
        ('Financial District', 'Richmond District'): 21/60,
        ('Financial District', 'Embarcadero'): 4/60,
        ('Financial District', 'Marina District'): 15/60,
        ('Marina District', 'Mission District'): 20/60,
        ('Marina District', 'Alamo Square'): 15/60,
        ('Marina District', 'Presidio'): 10/60,
        ('Marina District', 'Russian Hill'): 8/60,
        ('Marina District', 'North Beach'): 11/60,
        ('Marina District', 'Golden Gate Park'): 18/60,
        ('Marina District', 'Richmond District'): 11/60,
        ('Marina District', 'Embarcadero'): 14/60,
        ('Marina District', 'Financial District'): 17/60,
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Real(f'start_{name}')
        end = Real(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}

    # Current location starts at Mission District at 9:00 AM (9.0 hours)
    current_time = 9.0
    current_location = 'Mission District'

    # Track the order of meetings to enforce travel times
    meeting_order = []

    # Add constraints for each friend
    for name in friends:
        friend = friends[name]
        start_var = meeting_vars[name]['start']
        end_var = meeting_vars[name]['end']

        # Meeting must start within friend's availability window
        s.add(start_var >= friend['start'])
        s.add(end_var <= friend['end'])

        # Meeting duration must be at least the minimum required
        s.add(end_var - start_var >= friend['min_duration'])

        # Add travel time constraint from previous location to current friend's location
        if meeting_order:
            prev_name = meeting_order[-1]
            prev_location = friends[prev_name]['location']
            travel_time = travel_times[(prev_location, friend['location'])]
            s.add(start_var >= meeting_vars[prev_name]['end'] + travel_time)
        else:
            # First meeting must account for travel from Mission District
            travel_time = travel_times[(current_location, friend['location'])]
            s.add(start_var >= current_time + travel_time)

        meeting_order.append(name)

    # Try to solve the constraints
    if s.check() == sat:
        model = s.model()
        schedule = []
        for name in meeting_order:
            # Get the actual numerical values from the model
            start_val = model[meeting_vars[name]['start']]
            end_val = model[meeting_vars[name]['end']]
            
            # Convert to float values using eval
            start_float = float(str(start_val).split('?')[0])
            end_float = float(str(end_val).split('?')[0])
            
            schedule.append((name, start_float, end_float))
        
        # Sort schedule by start time
        schedule.sort(key=lambda x: x[1])
        
        # Print the schedule
        print("SOLUTION:")
        for name, start, end in schedule:
            start_hr = int(start)
            start_min = int(round((start - start_hr) * 60))
            end_hr = int(end)
            end_min = int(round((end - end_hr) * 60))
            
            # Handle minute overflow (e.g., 1.999 hours should be 2:00)
            if start_min >= 60:
                start_hr += 1
                start_min -= 60
            if end_min >= 60:
                end_hr += 1
                end_min -= 60
                
            print(f"Meet {name} at {friends[name]['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()