from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = {
        'William': {'location': 'Alamo Square', 'start': 15.25, 'end': 17.25, 'min_duration': 1.0},
        'Joshua': {'location': 'Richmond District', 'start': 7.0, 'end': 20.0, 'min_duration': 0.25},
        'Joseph': {'location': 'Financial District', 'start': 11.25, 'end': 13.5, 'min_duration': 0.25},
        'David': {'location': 'Union Square', 'start': 16.75, 'end': 19.25, 'min_duration': 0.75},
        'Brian': {'location': 'Fisherman\'s Wharf', 'start': 13.75, 'end': 20.75, 'min_duration': 1.75},
        'Karen': {'location': 'Marina District', 'start': 11.5, 'end': 18.5, 'min_duration': 0.25},
        'Anthony': {'location': 'Haight-Ashbury', 'start': 7.25, 'end': 10.5, 'min_duration': 0.5},
        'Matthew': {'location': 'Mission District', 'start': 17.25, 'end': 19.25, 'min_duration': 2.0},
        'Helen': {'location': 'Pacific Heights', 'start': 8.0, 'end': 12.0, 'min_duration': 1.25},
        'Jeffrey': {'location': 'Golden Gate Park', 'start': 19.0, 'end': 21.5, 'min_duration': 1.0}
    }

    # Travel times dictionary (simplified for the solver)
    travel_times = {
        ('The Castro', 'Alamo Square'): 8/60,
        ('The Castro', 'Richmond District'): 16/60,
        ('The Castro', 'Financial District'): 21/60,
        ('The Castro', 'Union Square'): 19/60,
        ('The Castro', 'Fisherman\'s Wharf'): 24/60,
        ('The Castro', 'Marina District'): 21/60,
        ('The Castro', 'Haight-Ashbury'): 6/60,
        ('The Castro', 'Mission District'): 7/60,
        ('The Castro', 'Pacific Heights'): 16/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('Alamo Square', 'The Castro'): 8/60,
        ('Alamo Square', 'Richmond District'): 11/60,
        ('Alamo Square', 'Financial District'): 17/60,
        ('Alamo Square', 'Union Square'): 14/60,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19/60,
        ('Alamo Square', 'Marina District'): 15/60,
        ('Alamo Square', 'Haight-Ashbury'): 5/60,
        ('Alamo Square', 'Mission District'): 10/60,
        ('Alamo Square', 'Pacific Heights'): 10/60,
        ('Alamo Square', 'Golden Gate Park'): 9/60,
        ('Richmond District', 'The Castro'): 16/60,
        ('Richmond District', 'Alamo Square'): 13/60,
        ('Richmond District', 'Financial District'): 22/60,
        ('Richmond District', 'Union Square'): 21/60,
        ('Richmond District', 'Fisherman\'s Wharf'): 18/60,
        ('Richmond District', 'Marina District'): 9/60,
        ('Richmond District', 'Haight-Ashbury'): 10/60,
        ('Richmond District', 'Mission District'): 20/60,
        ('Richmond District', 'Pacific Heights'): 10/60,
        ('Richmond District', 'Golden Gate Park'): 9/60,
        ('Financial District', 'The Castro'): 20/60,
        ('Financial District', 'Alamo Square'): 17/60,
        ('Financial District', 'Richmond District'): 21/60,
        ('Financial District', 'Union Square'): 9/60,
        ('Financial District', 'Fisherman\'s Wharf'): 10/60,
        ('Financial District', 'Marina District'): 15/60,
        ('Financial District', 'Haight-Ashbury'): 19/60,
        ('Financial District', 'Mission District'): 17/60,
        ('Financial District', 'Pacific Heights'): 13/60,
        ('Financial District', 'Golden Gate Park'): 23/60,
        ('Union Square', 'The Castro'): 17/60,
        ('Union Square', 'Alamo Square'): 15/60,
        ('Union Square', 'Richmond District'): 20/60,
        ('Union Square', 'Financial District'): 9/60,
        ('Union Square', 'Fisherman\'s Wharf'): 15/60,
        ('Union Square', 'Marina District'): 18/60,
        ('Union Square', 'Haight-Ashbury'): 18/60,
        ('Union Square', 'Mission District'): 14/60,
        ('Union Square', 'Pacific Heights'): 15/60,
        ('Union Square', 'Golden Gate Park'): 22/60,
        ('Fisherman\'s Wharf', 'The Castro'): 27/60,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21/60,
        ('Fisherman\'s Wharf', 'Richmond District'): 18/60,
        ('Fisherman\'s Wharf', 'Financial District'): 11/60,
        ('Fisherman\'s Wharf', 'Union Square'): 13/60,
        ('Fisherman\'s Wharf', 'Marina District'): 9/60,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22/60,
        ('Fisherman\'s Wharf', 'Mission District'): 22/60,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12/60,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25/60,
        ('Marina District', 'The Castro'): 22/60,
        ('Marina District', 'Alamo Square'): 15/60,
        ('Marina District', 'Richmond District'): 11/60,
        ('Marina District', 'Financial District'): 17/60,
        ('Marina District', 'Union Square'): 16/60,
        ('Marina District', 'Fisherman\'s Wharf'): 10/60,
        ('Marina District', 'Haight-Ashbury'): 16/60,
        ('Marina District', 'Mission District'): 20/60,
        ('Marina District', 'Pacific Heights'): 7/60,
        ('Marina District', 'Golden Gate Park'): 18/60,
        ('Haight-Ashbury', 'The Castro'): 6/60,
        ('Haight-Ashbury', 'Alamo Square'): 5/60,
        ('Haight-Ashbury', 'Richmond District'): 10/60,
        ('Haight-Ashbury', 'Financial District'): 21/60,
        ('Haight-Ashbury', 'Union Square'): 19/60,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23/60,
        ('Haight-Ashbury', 'Marina District'): 17/60,
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Pacific Heights'): 12/60,
        ('Haight-Ashbury', 'Golden Gate Park'): 7/60,
        ('Mission District', 'The Castro'): 7/60,
        ('Mission District', 'Alamo Square'): 11/60,
        ('Mission District', 'Richmond District'): 20/60,
        ('Mission District', 'Financial District'): 15/60,
        ('Mission District', 'Union Square'): 15/60,
        ('Mission District', 'Fisherman\'s Wharf'): 22/60,
        ('Mission District', 'Marina District'): 19/60,
        ('Mission District', 'Haight-Ashbury'): 12/60,
        ('Mission District', 'Pacific Heights'): 16/60,
        ('Mission District', 'Golden Gate Park'): 17/60,
        ('Pacific Heights', 'The Castro'): 16/60,
        ('Pacific Heights', 'Alamo Square'): 10/60,
        ('Pacific Heights', 'Richmond District'): 12/60,
        ('Pacific Heights', 'Financial District'): 13/60,
        ('Pacific Heights', 'Union Square'): 12/60,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13/60,
        ('Pacific Heights', 'Marina District'): 6/60,
        ('Pacific Heights', 'Haight-Ashbury'): 11/60,
        ('Pacific Heights', 'Mission District'): 15/60,
        ('Pacific Heights', 'Golden Gate Park'): 15/60,
        ('Golden Gate Park', 'The Castro'): 13/60,
        ('Golden Gate Park', 'Alamo Square'): 9/60,
        ('Golden Gate Park', 'Richmond District'): 7/60,
        ('Golden Gate Park', 'Financial District'): 26/60,
        ('Golden Gate Park', 'Union Square'): 22/60,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24/60,
        ('Golden Gate Park', 'Marina District'): 16/60,
        ('Golden Gate Park', 'Haight-Ashbury'): 7/60,
        ('Golden Gate Park', 'Mission District'): 17/60,
        ('Golden Gate Park', 'Pacific Heights'): 16/60
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Real(f'start_{name}')
        end = Real(f'end_{name}')
        meeting_vars[name] = {'start': start, 'end': end}

    # Create a variable to indicate if a friend is met
    met = {}
    for name in friends:
        met[name] = Bool(f'met_{name}')

    # Constraints for each friend's availability and duration if met
    for name in friends:
        friend = friends[name]
        start = meeting_vars[name]['start']
        end = meeting_vars[name]['end']
        s.add(Implies(met[name], start >= friend['start']))
        s.add(Implies(met[name], end <= friend['end']))
        s.add(Implies(met[name], end - start >= friend['min_duration']))

    # Initial location is The Castro at 9:00 AM
    current_time = 9.0
    current_location = 'The Castro'

    # We need to meet exactly 9 friends
    s.add(Sum([If(met[name], 1, 0) for name in friends]) == 9)

    # Order of meetings (this is a simplification; in practice, we'd need to explore all permutations)
    # Here, we prioritize friends with tighter time windows first
    meeting_order = ['Anthony', 'Helen', 'Joseph', 'Karen', 'Brian', 'William', 'David', 'Matthew', 'Jeffrey', 'Joshua']

    # Constraints for travel time between meetings
    prev_end = current_time
    prev_location = current_location
    for name in meeting_order:
        current_meeting = meeting_vars[name]
        current_location_friend = friends[name]['location']

        # Travel time from previous location to current location
        travel_key = (prev_location, current_location_friend)
        if travel_key in travel_times:
            travel_time = travel_times[travel_key]
        else:
            # Assume symmetric travel times if not explicitly given
            travel_key = (current_location_friend, prev_location)
            if travel_key in travel_times:
                travel_time = travel_times[travel_key]
            else:
                # Default travel time if not found (this is a simplification)
                travel_time = 0.5  # 30 minutes as a fallback

        # If we meet this friend, ensure the start time is after the previous end time plus travel time
        s.add(Implies(met[name], current_meeting['start'] >= prev_end + travel_time))

        # Update previous end time and location if we meet this friend
        prev_end = If(met[name], current_meeting['end'], prev_end)
        prev_location = If(met[name], current_location_friend, prev_location)

    # Ensure all meetings are scheduled if met
    for name in friends:
        s.add(Implies(met[name], meeting_vars[name]['start'] >= 0))
        s.add(Implies(met[name], meeting_vars[name]['end'] >= 0))

    # Check if a valid schedule exists
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m[met[name]]):
                start = m[meeting_vars[name]['start']]
                end = m[meeting_vars[name]['end']]
                schedule.append((name, float(start.as_decimal(10)), float(end.as_decimal(10))))
        
        # Sort schedule by start time
        schedule.sort(key=lambda x: x[1])
        
        # Print the schedule
        print("SOLUTION:")
        for name, start, end in schedule:
            start_str = f"{int(start)}:{int((start % 1) * 60):02d}"
            end_str = f"{int(end)}:{int((end % 1) * 60):02d}"
            print(f"Meet {name} at {friends[name]['location']} from {start_str} to {end_str}")
    else:
        print("No valid schedule found.")

solve_scheduling()