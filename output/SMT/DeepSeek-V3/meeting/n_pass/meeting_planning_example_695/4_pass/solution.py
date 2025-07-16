from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their details (times in hours)
    friends = {
        'Paul': {'location': 'Nob Hill', 'available_start': 16.25, 'available_end': 21.25, 'duration': 1.0},
        'Carol': {'location': 'Union Square', 'available_start': 18.0, 'available_end': 20.25, 'duration': 2.0},
        'Patricia': {'location': 'Chinatown', 'available_start': 20.0, 'available_end': 21.5, 'duration': 1.25},
        'Karen': {'location': 'The Castro', 'available_start': 17.0, 'available_end': 19.0, 'duration': 0.75},
        'Nancy': {'location': 'Presidio', 'available_start': 11.75, 'available_end': 22.0, 'duration': 0.5},
        'Jeffrey': {'location': 'Pacific Heights', 'available_start': 20.0, 'available_end': 20.75, 'duration': 0.75},
        'Matthew': {'location': 'Russian Hill', 'available_start': 15.75, 'available_end': 21.75, 'duration': 1.25}
    }

    # Travel times in hours (converted from minutes)
    travel_times = {
        'Bayview': {'Nob Hill': 20/60, 'Union Square': 17/60, 'Chinatown': 18/60,
                   'The Castro': 20/60, 'Presidio': 31/60, 'Pacific Heights': 23/60,
                   'Russian Hill': 23/60},
        'Nob Hill': {'Bayview': 19/60, 'Union Square': 7/60, 'Chinatown': 6/60,
                    'The Castro': 17/60, 'Presidio': 17/60, 'Pacific Heights': 8/60,
                    'Russian Hill': 5/60},
        # ... (other locations' travel times remain the same)
    }

    # Create variables for each friend's meeting
    start_times = {friend: Real(f'start_{friend}') for friend in friends}
    end_times = {friend: Real(f'end_{friend}') for friend in friends}

    # Initial conditions
    current_time = Real('initial_time')
    s.add(current_time == 9.0)  # Start at Bayview at 9:00 AM
    current_location = 'Bayview'

    # Create a list to track meeting order
    meeting_order = []

    # Add constraints for each friend
    for friend in friends:
        details = friends[friend]
        
        # Meeting must happen within availability window
        s.add(start_times[friend] >= details['available_start'])
        s.add(end_times[friend] <= details['available_end'])
        s.add(end_times[friend] == start_times[friend] + details['duration'])
        
        # Travel time constraint
        travel_time = travel_times[current_location][details['location']]
        s.add(start_times[friend] >= current_time + travel_time)
        
        # Update current time and location
        current_time = end_times[friend]
        current_location = details['location']
        meeting_order.append(friend)

    # Ensure meetings don't overlap
    for i in range(len(meeting_order)-1):
        friend1 = meeting_order[i]
        friend2 = meeting_order[i+1]
        travel = travel_times[friends[friend1]['location']][friends[friend2]['location']]
        s.add(start_times[friend2] >= end_times[friend1] + travel)

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        schedule = []
        
        for friend in friends:
            # Safely evaluate and convert times
            start_val = model.eval(start_times[friend])
            end_val = model.eval(end_times[friend])
            
            try:
                start = float(str(start_val))
                end = float(str(end_val))
            except:
                # Handle fraction case (e.g., 17/4)
                if '/' in str(start_val):
                    num, den = map(float, str(start_val).split('/'))
                    start = num / den
                else:
                    start = float(str(start_val))
                
                if '/' in str(end_val):
                    num, den = map(float, str(end_val).split('/'))
                    end = num / den
                else:
                    end = float(str(end_val))
            
            schedule.append((friend, start, end))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        
        # Print the schedule
        print("SOLUTION:")
        for friend, start, end in schedule:
            start_h = int(start)
            start_m = int((start - start_h) * 60)
            end_h = int(end)
            end_m = int((end - end_h) * 60)
            print(f"Meet {friend} at {friends[friend]['location']} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()