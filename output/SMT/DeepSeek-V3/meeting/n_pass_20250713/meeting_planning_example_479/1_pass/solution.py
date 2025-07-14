from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define locations and friends
    locations = ['Embarcadero', 'Golden Gate Park', 'Haight-Ashbury', 'Bayview', 'Presidio', 'Financial District']
    friends = {
        'Mary': {'location': 'Golden Gate Park', 'start': 8.75, 'end': 11.75, 'duration': 0.75},
        'Kevin': {'location': 'Haight-Ashbury', 'start': 10.25, 'end': 16.25, 'duration': 1.5},
        'Deborah': {'location': 'Bayview', 'start': 15.0, 'end': 19.25, 'duration': 2.0},
        'Stephanie': {'location': 'Presidio', 'start': 10.0, 'end': 17.25, 'duration': 2.0},
        'Emily': {'location': 'Financial District', 'start': 11.5, 'end': 21.75, 'duration': 1.75}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Embarcadero': {
            'Golden Gate Park': 25/60,
            'Haight-Ashbury': 21/60,
            'Bayview': 21/60,
            'Presidio': 20/60,
            'Financial District': 5/60
        },
        'Golden Gate Park': {
            'Embarcadero': 25/60,
            'Haight-Ashbury': 7/60,
            'Bayview': 23/60,
            'Presidio': 11/60,
            'Financial District': 26/60
        },
        'Haight-Ashbury': {
            'Embarcadero': 20/60,
            'Golden Gate Park': 7/60,
            'Bayview': 18/60,
            'Presidio': 15/60,
            'Financial District': 21/60
        },
        'Bayview': {
            'Embarcadero': 19/60,
            'Golden Gate Park': 22/60,
            'Haight-Ashbury': 19/60,
            'Presidio': 31/60,
            'Financial District': 19/60
        },
        'Presidio': {
            'Embarcadero': 20/60,
            'Golden Gate Park': 12/60,
            'Haight-Ashbury': 15/60,
            'Bayview': 31/60,
            'Financial District': 23/60
        },
        'Financial District': {
            'Embarcadero': 4/60,
            'Golden Gate Park': 23/60,
            'Haight-Ashbury': 19/60,
            'Bayview': 19/60,
            'Presidio': 22/60
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}

    # Current location starts at Embarcadero at 9:00 AM (9.0)
    current_time = 9.0
    current_location = 'Embarcadero'

    # To keep track of the order of meetings
    meeting_order = []

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(meeting_start[name] >= friend['start'])
        s.add(meeting_end[name] <= friend['end'])
        s.add(meeting_end[name] == meeting_start[name] + friend['duration'])

    # Ensure meetings don't overlap and account for travel time
    # We need to decide the order of meetings. This is a complex part and may require additional constraints.
    # For simplicity, we'll assume a specific order and add constraints accordingly.
    # A better approach would be to use a more sophisticated scheduling algorithm or allow the solver to choose the order.

    # Let's assume the order is Mary, Kevin, Stephanie, Deborah, Emily
    # This is a heuristic and may not be optimal; a more robust solution would explore all possible orders.
    order = ['Mary', 'Kevin', 'Stephanie', 'Deborah', 'Emily']

    for i in range(len(order)):
        name = order[i]
        if i == 0:
            # First meeting: travel from Embarcadero to friend's location
            travel_time = travel_times[current_location][friends[name]['location']]
            s.add(meeting_start[name] >= current_time + travel_time)
        else:
            prev_name = order[i-1]
            prev_location = friends[prev_name]['location']
            travel_time = travel_times[prev_location][friends[name]['location']]
            s.add(meeting_start[name] >= meeting_end[prev_name] + travel_time)

    # Maximize the number of friends met (all in this case)
    # Alternatively, we could maximize total meeting time or other metrics.

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for name in order:
            start = m[meeting_start[name]].as_fraction()
            end = m[meeting_end[name]].as_fraction()
            print(f"Meet {name} at {friends[name]['location']} from {float(start):.2f} to {float(end):.2f}")
    else:
        print("No solution found")

solve_scheduling()