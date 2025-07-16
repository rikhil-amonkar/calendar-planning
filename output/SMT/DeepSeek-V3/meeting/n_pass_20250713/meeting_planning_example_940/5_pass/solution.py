from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their details with time in hours (e.g., 17.5 = 5:30 PM)
    friends = {
        'Kevin': {'location': 'Mission District', 'start': 20.75, 'end': 21.75, 'min_duration': 1.0},
        'Mark': {'location': 'Fisherman\'s Wharf', 'start': 17.25, 'end': 20.0, 'min_duration': 1.5},
        'Jessica': {'location': 'Russian Hill', 'start': 9.0, 'end': 15.0, 'min_duration': 2.0},
        'Jason': {'location': 'Marina District', 'start': 15.25, 'end': 21.75, 'min_duration': 2.0},
        'John': {'location': 'North Beach', 'start': 9.75, 'end': 18.0, 'min_duration': 0.25},
        'Karen': {'location': 'Chinatown', 'start': 16.75, 'end': 19.0, 'min_duration': 1.25},
        'Sarah': {'location': 'Pacific Heights', 'start': 17.5, 'end': 18.25, 'min_duration': 0.75},
        'Amanda': {'location': 'The Castro', 'start': 20.0, 'end': 21.25, 'min_duration': 1.0},
        'Nancy': {'location': 'Nob Hill', 'start': 9.75, 'end': 13.0, 'min_duration': 0.75},
        'Rebecca': {'location': 'Sunset District', 'start': 8.75, 'end': 15.0, 'min_duration': 1.25}
    }

    # Create variables for each friend's meeting start and end times
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        # If meeting the friend, enforce availability and duration
        s.add(Implies(meet[name], And(
            meeting_start[name] >= friend['start'],
            meeting_end[name] <= friend['end'],
            meeting_end[name] - meeting_start[name] >= friend['min_duration']
        )))
        # If not meeting, set times to 0
        s.add(Implies(Not(meet[name]), And(
            meeting_start[name] == 0,
            meeting_end[name] == 0
        )))

    # Constraint to meet exactly 8 people
    s.add(Sum([If(meet[name], 1, 0) for name in friends]) == 8)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule (Meeting exactly 8 people):")
        
        # Create list of meetings sorted by start time
        scheduled_meetings = []
        for name in friends:
            if is_true(m.evaluate(meet[name])):
                start = m.evaluate(meeting_start[name])
                end = m.evaluate(meeting_end[name])
                scheduled_meetings.append((name, float(str(start)), float(str(end))))
        
        # Sort by start time and print
        scheduled_meetings.sort(key=lambda x: x[1])
        total_met = 0
        for name, start, end in scheduled_meetings:
            total_met += 1
            print(f"Meet {name} at {friends[name]['location']} from {start:.2f} to {end:.2f}")
        print(f"Total friends met: {total_met}")
    else:
        print("No feasible schedule found.")

solve_scheduling()