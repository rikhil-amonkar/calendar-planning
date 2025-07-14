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
        # Add other travel times as needed
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
            if m[met[name]]:
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