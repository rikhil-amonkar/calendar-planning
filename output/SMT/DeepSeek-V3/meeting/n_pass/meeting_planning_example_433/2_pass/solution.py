from z3 import *

def solve_scheduling():
    # Initialize solver with optimization
    opt = Optimize()

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

    # Variables to indicate if a meeting is scheduled
    scheduled = {name: Bool(f'scheduled_{name}') for name in friends}

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        opt.add(Implies(scheduled[name], meeting_start[name] >= friend['start']))
        opt.add(Implies(scheduled[name], meeting_end[name] <= friend['end']))
        opt.add(Implies(scheduled[name], meeting_end[name] == meeting_start[name] + friend['min_duration']))

    # Constraints for travel times between meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times.get((loc1, loc2), 0)
                opt.add(Implies(And(scheduled[name1], scheduled[name2]),
                        Or(meeting_start[name2] >= meeting_end[name1] + travel_time,
                           meeting_start[name1] >= meeting_end[name2] + travel_time)))

    # Starting at Nob Hill at 9:00 AM (540 minutes)
    first_meeting_start = Int('first_meeting_start')
    opt.add(first_meeting_start >= 540)
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times.get(('Nob Hill', loc), 0)
        opt.add(Implies(scheduled[name], meeting_start[name] >= 540 + travel_time))

    # Objective: maximize the number of friends met
    total_met = Sum([If(scheduled[name], 1, 0) for name in friends])
    opt.maximize(total_met)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        print("Optimal schedule:")
        scheduled_friends = [name for name in friends if m.evaluate(scheduled[name])]
        for name in sorted(scheduled_friends, key=lambda x: m.evaluate(meeting_start[x]).as_long()):
            start = m.evaluate(meeting_start[name])
            end = m.evaluate(meeting_end[name])
            start_time = f"{start.as_long() // 60:02d}:{start.as_long() % 60:02d}"
            end_time = f"{end.as_long() // 60:02d}:{end.as_long() % 60:02d}"
            print(f"Meet {name} at {friends[name]['location']} from {start_time} to {end_time}")
        print(f"Total friends met: {m.evaluate(total_met)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()