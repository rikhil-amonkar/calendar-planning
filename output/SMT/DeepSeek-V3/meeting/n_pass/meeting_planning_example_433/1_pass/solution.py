from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and friends
    locations = ['Nob Hill', 'Richmond District', 'Financial District', 'North Beach', 'The Castro', 'Golden Gate Park']
    friends = {
        'Emily': {'location': 'Richmond District', 'start': 19*60, 'end': 21*60, 'min_duration': 15},
        'Margaret': {'location': 'Financial District', 'start': 16*60 + 30, 'end': 20*60 + 15, 'min_duration': 75},
        'Ronald': {'location': 'North Beach', 'start': 18*60 + 30, 'end': 19*60 + 30, 'min_duration': 45},
        'Deborah': {'location': 'The Castro', 'start': 13*60 + 45, 'end': 21*60 + 15, 'min_duration': 90},
        'Jeffrey': {'location': 'Golden Gate Park', 'start': 11*60 + 15, 'end': 14*60 + 30, 'min_duration': 120}
    }

    # Travel times matrix (in minutes)
    travel_times = {
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Golden Gate Park'): 23,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Financial District'): 20,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'The Castro'): 13,
    }

    # Variables for meeting start and end times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Variables for meeting order (whether meeting A is before meeting B)
    order = {}
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                order[(name1, name2)] = Bool(f'order_{name1}_{name2}')

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(meeting_start[name] >= friend['start'])
        s.add(meeting_end[name] <= friend['end'])
        s.add(meeting_end[name] == meeting_start[name] + friend['min_duration'])

    # Constraints for travel times between meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times.get((loc1, loc2), 0)
                s.add(Implies(order[(name1, name2)], meeting_start[name2] >= meeting_end[name1] + travel_time))

    # Ensure order is consistent (either A before B or B before A)
    for name1 in friends:
        for name2 in friends:
            if name1 < name2:
                s.add(Xor(order[(name1, name2)], order[(name2, name1)]))

    # Starting at Nob Hill at 9:00 AM (540 minutes)
    first_meeting_start = Int('first_meeting_start')
    s.add(first_meeting_start >= 540)
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times.get(('Nob Hill', loc), 0)
        s.add(Implies(order[('Nob Hill', name)], meeting_start[name] >= 540 + travel_time))

    # Maximize the number of friends met (sum of booleans indicating if a meeting is scheduled)
    met = {name: Bool(f'met_{name}') for name in friends}
    for name in friends:
        s.add(met[name] == And(meeting_start[name] >= friends[name]['start'], meeting_end[name] <= friends[name]['end']))

    # Objective: maximize the number of friends met
    objective = Sum([If(met[name], 1, 0) for name in friends])
    maximize_objective = maximize(objective)
    s.add(maximize_objective)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule:")
        for name in sorted(friends.keys(), key=lambda x: m.evaluate(meeting_start[x]).as_long()):
            start = m.evaluate(meeting_start[name])
            end = m.evaluate(meeting_end[name])
            print(f"Meet {name} at {friends[name]['location']} from {start} to {end}")
        print(f"Total friends met: {m.evaluate(objective)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()