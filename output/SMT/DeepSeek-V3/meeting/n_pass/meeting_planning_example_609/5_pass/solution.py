from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends and their details
    friends = {
        'David': {'location': 'Mission District', 'start': 8*60, 'end': 19*60 + 45, 'duration': 45},
        'Kenneth': {'location': 'Alamo Square', 'start': 14*60, 'end': 19*60 + 45, 'duration': 120},
        'John': {'location': 'Pacific Heights', 'start': 17*60, 'end': 20*60, 'duration': 15},
        'Charles': {'location': 'Union Square', 'start': 21*60 + 45, 'end': 22*60 + 45, 'duration': 60},
        'Deborah': {'location': 'Golden Gate Park', 'start': 7*60, 'end': 18*60 + 15, 'duration': 90},
        'Karen': {'location': 'Sunset District', 'start': 17*60 + 45, 'end': 21*60 + 15, 'duration': 15},
        'Carol': {'location': 'Presidio', 'start': 8*60 + 15, 'end': 9*60 + 15, 'duration': 30}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Chinatown': {
            'Mission District': 18,
            'Alamo Square': 17,
            'Pacific Heights': 10,
            'Union Square': 7,
            'Golden Gate Park': 23,
            'Sunset District': 29,
            'Presidio': 19
        },
        'Mission District': {
            'Chinatown': 16,
            'Alamo Square': 11,
            'Pacific Heights': 16,
            'Union Square': 15,
            'Golden Gate Park': 17,
            'Sunset District': 24,
            'Presidio': 25
        },
        'Alamo Square': {
            'Chinatown': 16,
            'Mission District': 10,
            'Pacific Heights': 10,
            'Union Square': 14,
            'Golden Gate Park': 9,
            'Sunset District': 16,
            'Presidio': 18
        },
        'Pacific Heights': {
            'Chinatown': 11,
            'Mission District': 15,
            'Alamo Square': 10,
            'Union Square': 12,
            'Golden Gate Park': 15,
            'Sunset District': 21,
            'Presidio': 11
        },
        'Union Square': {
            'Chinatown': 7,
            'Mission District': 14,
            'Alamo Square': 15,
            'Pacific Heights': 15,
            'Golden Gate Park': 22,
            'Sunset District': 26,
            'Presidio': 24
        },
        'Golden Gate Park': {
            'Chinatown': 23,
            'Mission District': 17,
            'Alamo Square': 10,
            'Pacific Heights': 16,
            'Union Square': 22,
            'Sunset District': 10,
            'Presidio': 11
        },
        'Sunset District': {
            'Chinatown': 30,
            'Mission District': 24,
            'Alamo Square': 17,
            'Pacific Heights': 21,
            'Union Square': 30,
            'Golden Gate Park': 11,
            'Presidio': 16
        },
        'Presidio': {
            'Chinatown': 21,
            'Mission District': 26,
            'Alamo Square': 18,
            'Pacific Heights': 11,
            'Union Square': 22,
            'Golden Gate Park': 12,
            'Sunset District': 15
        }
    }

    # Variables for each friend's meeting
    meet_vars = {friend: Bool(f'meet_{friend}') for friend in friends}
    start_vars = {friend: Int(f'start_{friend}') for friend in friends}
    end_vars = {friend: Int(f'end_{friend}') for friend in friends}

    # Current location starts at Chinatown at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Chinatown'

    # Basic constraints for each friend
    for friend in friends:
        s.add(Implies(meet_vars[friend], start_vars[friend] >= friends[friend]['start']))
        s.add(Implies(meet_vars[friend], end_vars[friend] <= friends[friend]['end']))
        s.add(Implies(meet_vars[friend], end_vars[friend] == start_vars[friend] + friends[friend]['duration']))

    # Carol must be met first if at all (since she's only available early)
    s.add(Implies(meet_vars['Carol'], 
                 And(start_vars['Carol'] >= current_time + travel_times[current_location]['Presidio'],
                     start_vars['Carol'] <= friends['Carol']['end'] - friends['Carol']['duration'])))

    # Sequence constraints for other friends
    # After Carol (if met), we can meet others
    for friend in ['David', 'Deborah', 'Kenneth', 'John', 'Karen', 'Charles']:
        # Find all possible predecessors
        predecessors = []
        if friend == 'David':
            predecessors = [('Carol', 'Presidio')]
        elif friend == 'Deborah':
            predecessors = [('David', 'Mission District'), ('Carol', 'Presidio')]
        elif friend == 'Kenneth':
            predecessors = [('Deborah', 'Golden Gate Park'), ('David', 'Mission District')]
        elif friend == 'John':
            predecessors = [('Kenneth', 'Alamo Square'), ('Deborah', 'Golden Gate Park')]
        elif friend == 'Karen':
            predecessors = [('John', 'Pacific Heights'), ('Kenneth', 'Alamo Square')]
        elif friend == 'Charles':
            predecessors = [('Karen', 'Sunset District'), ('John', 'Pacific Heights')]

        # Add constraints for each possible predecessor
        for pred, loc in predecessors:
            s.add(Implies(And(meet_vars[pred], meet_vars[friend]),
                         start_vars[friend] >= end_vars[pred] + travel_times[loc][friends[friend]['location']]))

    # If not meeting any predecessor, can meet from Chinatown
    for friend in ['David', 'Deborah', 'Kenneth', 'John', 'Karen', 'Charles']:
        s.add(Implies(And(Not(Or([meet_vars[pred] for pred, _ in [
            ('Carol', 'Presidio') if friend == 'David' else
            ('David', 'Mission District') if friend == 'Deborah' else
            ('Deborah', 'Golden Gate Park') if friend == 'Kenneth' else
            ('Kenneth', 'Alamo Square') if friend == 'John' else
            ('John', 'Pacific Heights') if friend == 'Karen' else
            ('Karen', 'Sunset District')
        ]])), meet_vars[friend]),
                     start_vars[friend] >= current_time + travel_times[current_location][friends[friend]['location']]))

    # Objective: maximize the number of friends met
    s.maximize(Sum([If(meet_vars[friend], 1, 0) for friend in friends]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found:")
        total_met = 0
        schedule = []
        
        for friend in friends:
            if m.evaluate(meet_vars[friend]):
                total_met += 1
                start = m.evaluate(start_vars[friend]).as_long()
                end = m.evaluate(end_vars[friend]).as_long()
                start_time = f"{start//60:02d}:{start%60:02d}"
                end_time = f"{end//60:02d}:{end%60:02d}"
                schedule.append((friend, friends[friend]['location'], start_time, end_time))
        
        # Sort schedule by start time
        schedule.sort(key=lambda x: (int(x[2].split(':')[0]), int(x[2].split(':')[1])))
        
        print(f"Total friends met: {total_met}")
        for meet in schedule:
            print(f"Meet {meet[0]} at {meet[1]} from {meet[2]} to {meet[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()