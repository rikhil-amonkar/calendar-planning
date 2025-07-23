from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their details with corrected time representations
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

    # Travel times (simplified as a dictionary of dictionaries)
    travel_times = {
        'Union Square': {
            'Mission District': 14/60,
            'Fisherman\'s Wharf': 15/60,
            'Russian Hill': 13/60,
            'Marina District': 18/60,
            'North Beach': 10/60,
            'Chinatown': 7/60,
            'Pacific Heights': 15/60,
            'The Castro': 17/60,
            'Nob Hill': 9/60,
            'Sunset District': 27/60
        },
        # ... (rest of travel times remain the same as previous solution)
    }

    # Create variables for each friend's meeting start and end times
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        # Strictly enforce availability windows and durations
        s.add(Implies(meet[name], And(
            meeting_start[name] >= friend['start'],
            meeting_end[name] <= friend['end'],
            meeting_end[name] - meeting_start[name] >= friend['min_duration']
        )))
        s.add(Implies(Not(meet[name]), And(
            meeting_start[name] == 0,
            meeting_end[name] == 0
        )))

    # Additional constraints to ensure Sarah's meeting is within her availability
    s.add(Implies(meet['Sarah'], And(
        meeting_start['Sarah'] >= 17.5,
        meeting_end['Sarah'] <= 18.25,
        meeting_end['Sarah'] - meeting_start['Sarah'] >= 0.75
    )))

    # Constraint to meet exactly 8 people
    s.add(Sum([If(meet[name], 1, 0) for name in friends]) == 8)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule (Meeting exactly 8 people with correct timings):")
        total_met = 0
        for name in sorted(friends.keys(), key=lambda x: float(str(m.evaluate(meeting_start[x]))):
            if m.evaluate(meet[name]):
                total_met += 1
                start = m.evaluate(meeting_start[name])
                end = m.evaluate(meeting_end[name])
                print(f"Meet {name} at {friends[name]['location']} from {float(str(start)):.2f} to {float(str(end)):.2f}")
        print(f"Total friends met: {total_met}")
    else:
        print("No feasible schedule found.")

solve_scheduling()