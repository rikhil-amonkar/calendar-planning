from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends data with consistent naming
    friends = [
        {'name': 'Linda', 'location': 'Marina District', 'start': 18*60, 'end': 22*60, 'duration': 30},
        {'name': 'Kenneth', 'location': 'The Castro', 'start': 14*60 + 45, 'end': 16*60 + 15, 'duration': 30},
        {'name': 'Kimberly', 'location': 'Richmond District', 'start': 14*60 + 15, 'end': 22*60, 'duration': 30},
        {'name': 'Paul', 'location': 'Alamo Square', 'start': 21*60, 'end': 21*60 + 30, 'duration': 15},
        {'name': 'Carol', 'location': 'Financial District', 'start': 10*60 + 15, 'end': 12*60, 'duration': 60},
        {'name': 'Brian', 'location': 'Presidio', 'start': 10*60, 'end': 21*60 + 30, 'duration': 75},
        {'name': 'Laura', 'location': 'Mission District', 'start': 16*60 + 15, 'end': 20*60 + 30, 'duration': 30},
        {'name': 'Sandra', 'location': 'Nob Hill', 'start': 9*60 + 15, 'end': 18*60 + 30, 'duration': 60},
        {'name': 'Karen', 'location': 'Russian Hill', 'start': 18*60 + 30, 'end': 22*60, 'duration': 75}
    ]

    # Consistent travel times dictionary
    travel_times = {
        'Pacific Heights': {'Marina District': 6, 'The Castro': 16, 'Richmond District': 12, 
                           'Alamo Square': 10, 'Financial District': 13, 'Presidio': 11,
                           'Mission District': 15, 'Nob Hill': 8, 'Russian Hill': 7},
        'Marina District': {'Pacific Heights': 7, 'The Castro': 22, 'Richmond District': 11,
                           'Alamo Square': 15, 'Financial District': 17, 'Presidio': 10,
                           'Mission District': 20, 'Nob Hill': 12, 'Russian Hill': 8},
        # ... (other locations with consistent naming)
    }

    # Create variables for each meeting
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        scheduled = Bool(f"scheduled_{friend['name']}")
        meeting_vars.append({
            'name': friend['name'],
            'location': friend['location'],
            'start': start,
            'end': end,
            'scheduled': scheduled,
            'min_start': friend['start'],
            'max_end': friend['end'],
            'duration': friend['duration']
        })

    # Current location and time
    current_loc = 'Pacific Heights'
    current_time = 9 * 60  # 9:00 AM

    # Add basic constraints
    for m in meeting_vars:
        s.add(Implies(m['scheduled'], And(
            m['start'] >= m['min_start'],
            m['end'] <= m['max_end'],
            m['end'] == m['start'] + m['duration'],
            m['start'] >= current_time + travel_times[current_loc][m['location']]
        )))
        s.add(Implies(Not(m['scheduled']), m['start'] == -1))

    # Add sequencing constraints
    for i in range(len(meeting_vars)):
        for j in range(i+1, len(meeting_vars)):
            m1 = meeting_vars[i]
            m2 = meeting_vars[j]
            travel = travel_times[m1['location']][m2['location']]
            s.add(Implies(And(m1['scheduled'], m2['scheduled']),
                        Or(m1['end'] + travel <= m2['start'],
                           m2['end'] + travel_times[m2['location']][m1['location']] <= m1['start'])))

    # Maximize number of scheduled meetings
    s.maximize(Sum([If(m['scheduled'], 1, 0) for m in meeting_vars]))

    # Solve and output
    if s.check() == sat:
        model = s.model()
        scheduled = []
        for m in meeting_vars:
            if is_true(model.evaluate(m['scheduled'])):
                start = model.evaluate(m['start']).as_long()
                end = model.evaluate(m['end']).as_long()
                scheduled.append((m['name'], m['location'], start, end))
        
        scheduled.sort(key=lambda x: x[2])  # Sort by start time
        print("Optimal Schedule:")
        for name, loc, start, end in scheduled:
            print(f"Meet {name} at {loc} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
    else:
        print("No feasible schedule found")

solve_scheduling()