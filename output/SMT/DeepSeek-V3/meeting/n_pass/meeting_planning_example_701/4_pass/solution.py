from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Friends' availability and constraints
    friends = {
        'Lisa': {'location': 'The Castro', 'start': time_to_minutes(19, 15), 'end': time_to_minutes(21, 15), 'duration': 120},
        'Daniel': {'location': 'Nob Hill', 'start': time_to_minutes(8, 15), 'end': time_to_minutes(11, 00), 'duration': 15},
        'Elizabeth': {'location': 'Presidio', 'start': time_to_minutes(21, 15), 'end': time_to_minutes(22, 15), 'duration': 45},
        'Steven': {'location': 'Marina District', 'start': time_to_minutes(16, 30), 'end': time_to_minutes(20, 45), 'duration': 90},
        'Timothy': {'location': 'Pacific Heights', 'start': time_to_minutes(12, 00), 'end': time_to_minutes(18, 00), 'duration': 90},
        'Ashley': {'location': 'Golden Gate Park', 'start': time_to_minutes(20, 45), 'end': time_to_minutes(21, 45), 'duration': 60},
        'Kevin': {'location': 'Chinatown', 'start': time_to_minutes(12, 00), 'end': time_to_minutes(19, 00), 'duration': 30},
        'Betty': {'location': 'Richmond District', 'start': time_to_minutes(13, 15), 'end': time_to_minutes(15, 45), 'duration': 30}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Mission District': {
            'The Castro': 7, 'Nob Hill': 12, 'Presidio': 25, 'Marina District': 19,
            'Pacific Heights': 16, 'Golden Gate Park': 17, 'Chinatown': 16, 'Richmond District': 20
        },
        'The Castro': {
            'Mission District': 7, 'Nob Hill': 16, 'Presidio': 20, 'Marina District': 21,
            'Pacific Heights': 16, 'Golden Gate Park': 11, 'Chinatown': 22, 'Richmond District': 16
        },
        'Nob Hill': {
            'Mission District': 13, 'The Castro': 17, 'Presidio': 17, 'Marina District': 11,
            'Pacific Heights': 8, 'Golden Gate Park': 17, 'Chinatown': 6, 'Richmond District': 14
        },
        'Presidio': {
            'Mission District': 26, 'The Castro': 21, 'Nob Hill': 18, 'Marina District': 11,
            'Pacific Heights': 11, 'Golden Gate Park': 12, 'Chinatown': 21, 'Richmond District': 7
        },
        'Marina District': {
            'Mission District': 20, 'The Castro': 22, 'Nob Hill': 12, 'Presidio': 10,
            'Pacific Heights': 7, 'Golden Gate Park': 18, 'Chinatown': 15, 'Richmond District': 11
        },
        'Pacific Heights': {
            'Mission District': 15, 'The Castro': 16, 'Nob Hill': 8, 'Presidio': 11,
            'Marina District': 6, 'Golden Gate Park': 15, 'Chinatown': 11, 'Richmond District': 12
        },
        'Golden Gate Park': {
            'Mission District': 17, 'The Castro': 13, 'Nob Hill': 20, 'Presidio': 11,
            'Marina District': 16, 'Pacific Heights': 16, 'Chinatown': 23, 'Richmond District': 7
        },
        'Chinatown': {
            'Mission District': 17, 'The Castro': 22, 'Nob Hill': 9, 'Presidio': 19,
            'Marina District': 12, 'Pacific Heights': 10, 'Golden Gate Park': 23, 'Richmond District': 20
        },
        'Richmond District': {
            'Mission District': 20, 'The Castro': 16, 'Nob Hill': 17, 'Presidio': 7,
            'Marina District': 9, 'Pacific Heights': 10, 'Golden Gate Park': 9, 'Chinatown': 20
        }
    }

    # Decision variables
    meet = {name: Bool(f"meet_{name}") for name in friends}
    start_times = {name: Int(f"start_{name}") for name in friends}
    end_times = {name: Int(f"end_{name}") for name in friends}

    # Base constraints
    for name in friends:
        info = friends[name]
        s.add(Implies(meet[name], start_times[name] >= info['start']))
        s.add(Implies(meet[name], end_times[name] <= info['end']))
        s.add(Implies(meet[name], end_times[name] == start_times[name] + info['duration']))

    # Sequencing constraints
    all_meetings = [(name, friends[name]['location']) for name in friends]
    for i in range(len(all_meetings)):
        for j in range(i+1, len(all_meetings)):
            name1, loc1 = all_meetings[i]
            name2, loc2 = all_meetings[j]
            travel = travel_times[loc1][loc2]
            s.add(Implies(And(meet[name1], meet[name2]),
                         Or(end_times[name1] + travel <= start_times[name2],
                            end_times[name2] + travel <= start_times[name1])))

    # Maximize number of friends met
    s.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    if s.check() == sat:
        model = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for name in friends:
            if model.evaluate(meet[name]):
                start = model.evaluate(start_times[name]).as_long()
                end = model.evaluate(end_times[name]).as_long()
                scheduled.append((name, start, end))
        
        scheduled.sort(key=lambda x: x[1])
        
        for name, start, end in scheduled:
            start_h = (start + 540) // 60
            start_m = (start + 540) % 60
            end_h = (end + 540) // 60
            end_m = (end + 540) % 60
            print(f"Meet {name} at {friends[name]['location']} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
        
        print(f"Total friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()