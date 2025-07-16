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

    # Variables for each friend's meeting start and end times, and whether they are met
    meet_vars = {}
    start_vars = {}
    end_vars = {}
    for friend in friends:
        meet_vars[friend] = Bool(f'meet_{friend}')
        start_vars[friend] = Int(f'start_{friend}')
        end_vars[friend] = Int(f'end_{friend}')

    # Current location starts at Chinatown at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Chinatown'

    # Constraints for each friend
    for friend in friends:
        s.add(Implies(meet_vars[friend], start_vars[friend] >= friends[friend]['start']))
        s.add(Implies(meet_vars[friend], end_vars[friend] <= friends[friend]['end']))
        s.add(Implies(meet_vars[friend], end_vars[friend] == start_vars[friend] + friends[friend]['duration']))

    # Constraints for travel times
    # We need to model the sequence of meetings. This is complex, so we'll assume a possible order.
    # For simplicity, let's assume we meet Carol first if possible, then others in a feasible order.

    # Carol is only available early, so handle her first if met.
    s.add(Implies(meet_vars['Carol'], start_vars['Carol'] >= current_time + travel_times[current_location]['Presidio']))
    # After meeting Carol, current time is end_vars['Carol'], location is Presidio.

    # For other friends, we'll add constraints based on possible sequences.
    # For example, after Carol, we can meet David, Deborah, etc.

    # David can be met after Carol if Carol is met.
    s.add(Implies(And(meet_vars['Carol'], meet_vars['David']), start_vars['David'] >= end_vars['Carol'] + travel_times['Presidio']['Mission District']))
    # If Carol is not met, David can be met from Chinatown.
    s.add(Implies(And(Not(meet_vars['Carol']), meet_vars['David']), start_vars['David'] >= current_time + travel_times['Chinatown']['Mission District']))

    # Similarly for other friends, adding constraints based on possible sequences.

    # Deborah can be met after David if David is met.
    s.add(Implies(And(meet_vars['David'], meet_vars['Deborah']), start_vars['Deborah'] >= end_vars['David'] + travel_times['Mission District']['Golden Gate Park']))
    # If David is not met, Deborah can be met from Chinatown or after Carol.
    s.add(Implies(And(Not(meet_vars['David']), meet_vars['Deborah']), start_vars['Deborah'] >= current_time + travel_times['Chinatown']['Golden Gate Park']))

    # Kenneth can be met after Deborah if Deborah is met.
    s.add(Implies(And(meet_vars['Deborah'], meet_vars['Kenneth']), start_vars['Kenneth'] >= end_vars['Deborah'] + travel_times['Golden Gate Park']['Alamo Square']))
    # If Deborah is not met, Kenneth can be met from Chinatown or after David.
    s.add(Implies(And(Not(meet_vars['Deborah']), meet_vars['Kenneth']), start_vars['Kenneth'] >= current_time + travel_times['Chinatown']['Alamo Square']))

    # John can be met after Kenneth if Kenneth is met.
    s.add(Implies(And(meet_vars['Kenneth'], meet_vars['John']), start_vars['John'] >= end_vars['Kenneth'] + travel_times['Alamo Square']['Pacific Heights']))
    # If Kenneth is not met, John can be met from Chinatown or after Deborah.
    s.add(Implies(And(Not(meet_vars['Kenneth']), meet_vars['John']), start_vars['John'] >= current_time + travel_times['Chinatown']['Pacific Heights']))

    # Karen can be met after John if John is met.
    s.add(Implies(And(meet_vars['John'], meet_vars['Karen']), start_vars['Karen'] >= end_vars['John'] + travel_times['Pacific Heights']['Sunset District']))
    # If John is not met, Karen can be met from Chinatown or after Kenneth.
    s.add(Implies(And(Not(meet_vars['John']), meet_vars['Karen']), start_vars['Karen'] >= current_time + travel_times['Chinatown']['Sunset District']))

    # Charles can be met after Karen if Karen is met.
    s.add(Implies(And(meet_vars['Karen'], meet_vars['Charles']), start_vars['Charles'] >= end_vars['Karen'] + travel_times['Sunset District']['Union Square']))
    # If Karen is not met, Charles can be met from Chinatown or after John.
    s.add(Implies(And(Not(meet_vars['Karen']), meet_vars['Charles']), start_vars['Charles'] >= current_time + travel_times['Chinatown']['Union Square']))

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
                start_time = f"{start // 60}:{start % 60:02d}"
                end_time = f"{end // 60}:{end % 60:02d}"
                schedule.append((friend, friends[friend]['location'], start_time, end_time))
        schedule.sort(key=lambda x: int(x[2].split(':')[0]) * 60 + int(x[2].split(':')[1]))
        print(f"Total friends met: {total_met}")
        for meet in schedule:
            print(f"Meet {meet[0]} at {meet[1]} from {meet[2]} to {meet[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()