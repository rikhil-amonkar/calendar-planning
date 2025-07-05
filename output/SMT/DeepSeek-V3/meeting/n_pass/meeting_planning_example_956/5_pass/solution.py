from z3 import *

def solve_scheduling():
    s = Solver()

    # Define friends data
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

    # Simplified travel times (minutes converted to hours)
    travel_times = {
        ('The Castro', 'Alamo Square'): 0.13,
        ('The Castro', 'Haight-Ashbury'): 0.1,
        ('The Castro', 'Mission District'): 0.12,
        ('Haight-Ashbury', 'Alamo Square'): 0.08,
        ('Alamo Square', 'Richmond District'): 0.18,
        ('Richmond District', 'Marina District'): 0.15,
        ('Marina District', 'Fisherman\'s Wharf'): 0.17,
        ('Fisherman\'s Wharf', 'Financial District'): 0.18,
        ('Financial District', 'Union Square'): 0.15,
        ('Union Square', 'Mission District'): 0.23,
        ('Mission District', 'Golden Gate Park'): 0.28,
        # Add more connections as needed
    }

    # Create variables
    meeting_vars = {}
    met = {}
    for name in friends:
        meeting_vars[name] = {
            'start': Real(f'start_{name}'),
            'end': Real(f'end_{name}')
        }
        met[name] = Bool(f'met_{name}')

    # Base constraints
    for name in friends:
        s.add(Implies(met[name], 
              And(meeting_vars[name]['start'] >= friends[name]['start'],
                  meeting_vars[name]['end'] <= friends[name]['end'],
                  meeting_vars[name]['end'] - meeting_vars[name]['start'] >= friends[name]['min_duration'])))

    # Must meet exactly 9 friends
    s.add(Sum([If(met[name], 1, 0) for name in friends]) == 9)

    # Initial conditions
    current_time = 9.0  # Start at 9:00 AM at The Castro
    current_location = 'The Castro'

    # Define a meeting order that makes geographic sense
    meeting_order = ['Anthony', 'Helen', 'Joseph', 'Karen', 'Brian', 'William', 'David', 'Matthew', 'Jeffrey', 'Joshua']

    # Travel constraints
    prev_end = current_time
    prev_location = current_location
    for name in meeting_order:
        loc = friends[name]['location']
        travel_key = (prev_location, loc)
        
        # Get travel time or use a default
        travel_time = travel_times.get(travel_key, 0.25)  # Default 15 minutes
        
        s.add(Implies(met[name], 
              meeting_vars[name]['start'] >= prev_end + travel_time))
        
        # Update previous end time and location if meeting this friend
        prev_end = If(met[name], meeting_vars[name]['end'], prev_end)
        prev_location = If(met[name], loc, prev_location)

    # Solve and print schedule
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m[met[name]]):
                start = m[meeting_vars[name]['start']]
                end = m[meeting_vars[name]['end']]
                schedule.append((name, float(start.as_decimal(10)), float(end.as_decimal(10))))
        
        schedule.sort(key=lambda x: x[1])
        
        print("SOLUTION:")
        for name, start, end in schedule:
            start_hr = int(start)
            start_min = int((start % 1) * 60)
            end_hr = int(end)
            end_min = int((end % 1) * 60)
            print(f"Meet {name} at {friends[name]['location']} from {start_hr}:{start_min:02d} to {end_hr}:{end_min:02d}")
        
        # Print who was skipped
        skipped = [name for name in friends if not is_true(m[met[name]])]
        print(f"\nSkipped meeting with: {skipped[0]}")
    else:
        print("No valid schedule found")

solve_scheduling()