from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        'Matthew': {'location': 'The Castro', 'start': 16.5, 'end': 20.0, 'duration': 0.75},
        'Rebecca': {'location': 'Nob Hill', 'start': 15.25, 'end': 19.25, 'duration': 1.75},
        'Brian': {'location': 'Marina District', 'start': 14.25, 'end': 22.0, 'duration': 0.5},
        'Emily': {'location': 'Pacific Heights', 'start': 11.25, 'end': 19.75, 'duration': 0.25},
        'Karen': {'location': 'Haight-Ashbury', 'start': 11.75, 'end': 17.5, 'duration': 0.5},
        'Stephanie': {'location': 'Mission District', 'start': 13.0, 'end': 15.75, 'duration': 1.25},
        'James': {'location': 'Chinatown', 'start': 14.5, 'end': 19.0, 'duration': 2.0},
        'Steven': {'location': 'Russian Hill', 'start': 14.0, 'end': 20.0, 'duration': 0.5},
        'Elizabeth': {'location': 'Alamo Square', 'start': 13.0, 'end': 17.25, 'duration': 2.0},
        'William': {'location': 'Bayview', 'start': 18.25, 'end': 20.25, 'duration': 1.5}
    }

    # Travel times dictionary (simplified for this problem)
    travel_times = {
        ('Richmond District', 'The Castro'): 16/60,
        ('Richmond District', 'Nob Hill'): 17/60,
        ('Richmond District', 'Marina District'): 9/60,
        ('Richmond District', 'Pacific Heights'): 10/60,
        ('Richmond District', 'Haight-Ashbury'): 10/60,
        ('Richmond District', 'Mission District'): 20/60,
        ('Richmond District', 'Chinatown'): 20/60,
        ('Richmond District', 'Russian Hill'): 13/60,
        ('Richmond District', 'Alamo Square'): 13/60,
        ('Richmond District', 'Bayview'): 27/60,
        ('The Castro', 'Nob Hill'): 16/60,
        ('The Castro', 'Marina District'): 21/60,
        ('The Castro', 'Pacific Heights'): 16/60,
        ('The Castro', 'Haight-Ashbury'): 6/60,
        ('The Castro', 'Mission District'): 7/60,
        ('The Castro', 'Chinatown'): 22/60,
        ('The Castro', 'Russian Hill'): 18/60,
        ('The Castro', 'Alamo Square'): 8/60,
        ('The Castro', 'Bayview'): 19/60,
        ('Nob Hill', 'Marina District'): 11/60,
        ('Nob Hill', 'Pacific Heights'): 8/60,
        ('Nob Hill', 'Haight-Ashbury'): 13/60,
        ('Nob Hill', 'Mission District'): 13/60,
        ('Nob Hill', 'Chinatown'): 6/60,
        ('Nob Hill', 'Russian Hill'): 5/60,
        ('Nob Hill', 'Alamo Square'): 11/60,
        ('Nob Hill', 'Bayview'): 19/60,
        ('Marina District', 'Pacific Heights'): 7/60,
        ('Marina District', 'Haight-Ashbury'): 16/60,
        ('Marina District', 'Mission District'): 20/60,
        ('Marina District', 'Chinatown'): 15/60,
        ('Marina District', 'Russian Hill'): 8/60,
        ('Marina District', 'Alamo Square'): 15/60,
        ('Marina District', 'Bayview'): 27/60,
        ('Pacific Heights', 'Haight-Ashbury'): 11/60,
        ('Pacific Heights', 'Mission District'): 15/60,
        ('Pacific Heights', 'Chinatown'): 11/60,
        ('Pacific Heights', 'Russian Hill'): 7/60,
        ('Pacific Heights', 'Alamo Square'): 10/60,
        ('Pacific Heights', 'Bayview'): 22/60,
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Chinatown'): 19/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Haight-Ashbury', 'Alamo Square'): 5/60,
        ('Haight-Ashbury', 'Bayview'): 18/60,
        ('Mission District', 'Chinatown'): 16/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Mission District', 'Alamo Square'): 11/60,
        ('Mission District', 'Bayview'): 14/60,
        ('Chinatown', 'Russian Hill'): 7/60,
        ('Chinatown', 'Alamo Square'): 17/60,
        ('Chinatown', 'Bayview'): 20/60,
        ('Russian Hill', 'Alamo Square'): 15/60,
        ('Russian Hill', 'Bayview'): 23/60,
        ('Alamo Square', 'Bayview'): 16/60
    }

    # Add symmetric travel times
    for (a, b), time in list(travel_times.items()):
        if (b, a) not in travel_times:
            travel_times[(b, a)] = time

    # Create variables for each friend's meeting start and end times
    meeting_starts = {name: Real(f'start_{name}') for name in friends}
    meeting_ends = {name: Real(f'end_{name}') for name in friends}

    # Constraints for each friend's availability and duration
    for name in friends:
        friend = friends[name]
        s.add(meeting_starts[name] >= friend['start'])
        s.add(meeting_ends[name] <= friend['end'])
        s.add(meeting_ends[name] == meeting_starts[name] + friend['duration'])

    # Current location starts at Richmond District at 9:00 AM (9.0 hours)
    current_time = 9.0
    current_location = 'Richmond District'

    # Track the order of meetings (simplified approach)
    # We'll assume a specific order to simplify the problem
    # This is a heuristic; a more comprehensive approach would involve sequencing variables
    # For this example, we'll prioritize friends with tighter windows first

    # Define a possible order (this is a heuristic and may need adjustment)
    order = ['Emily', 'Karen', 'Stephanie', 'Elizabeth', 'James', 'Steven', 'Brian', 'Rebecca', 'Matthew', 'William']
    
    # Add constraints for travel times between meetings
    prev_location = current_location
    prev_end = current_time
    for name in order:
        friend = friends[name]
        location = friend['location']
        travel_time = travel_times.get((prev_location, location), 0)
        s.add(meeting_starts[name] >= prev_end + travel_time)
        prev_location = location
        prev_end = meeting_ends[name]

    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            start = m[meeting_starts[name]].as_fraction()
            end = m[meeting_ends[name]].as_fraction()
            schedule.append((name, float(start), float(end)))
        schedule.sort(key=lambda x: x[1])
        print("Feasible schedule found:")
        for name, start, end in schedule:
            print(f"{name}: {start:.2f} - {end:.2f}")
    else:
        print("No feasible schedule found.")

solve_scheduling()