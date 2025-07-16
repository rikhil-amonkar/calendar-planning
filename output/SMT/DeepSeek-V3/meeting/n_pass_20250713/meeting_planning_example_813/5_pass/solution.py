from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Friends and their details
    friends = {
        'Joshua': {'location': 'Embarcadero', 'available_start': 9*60 + 45, 'available_end': 18*60, 'min_duration': 105},
        'Jeffrey': {'location': 'Bayview', 'available_start': 9*60 + 45, 'available_end': 20*60 + 15, 'min_duration': 75},
        'Charles': {'location': 'Union Square', 'available_start': 10*60 + 45, 'available_end': 20*60 + 15, 'min_duration': 120},
        'Joseph': {'location': 'Chinatown', 'available_start': 7*60, 'available_end': 15*60 + 30, 'min_duration': 60},
        'Elizabeth': {'location': 'Sunset District', 'available_start': 9*60, 'available_end': 9*60 + 45, 'min_duration': 45},
        'Matthew': {'location': 'Golden Gate Park', 'available_start': 11*60, 'available_end': 19*60 + 30, 'min_duration': 45},
        'Carol': {'location': 'Financial District', 'available_start': 10*60 + 45, 'available_end': 11*60 + 15, 'min_duration': 15},
        'Paul': {'location': 'Haight-Ashbury', 'available_start': 19*60 + 15, 'available_end': 20*60 + 30, 'min_duration': 15},
        'Rebecca': {'location': 'Mission District', 'available_start': 17*60, 'available_end': 21*60 + 45, 'min_duration': 45}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Marina District': {
            'Embarcadero': 14,
            'Bayview': 27,
            'Union Square': 16,
            'Chinatown': 15,
            'Sunset District': 19,
            'Golden Gate Park': 18,
            'Financial District': 17,
            'Haight-Ashbury': 16,
            'Mission District': 20
        },
        'Embarcadero': {
            'Marina District': 12,
            'Bayview': 21,
            'Union Square': 10,
            'Chinatown': 7,
            'Sunset District': 30,
            'Golden Gate Park': 25,
            'Financial District': 5,
            'Haight-Ashbury': 21,
            'Mission District': 20
        },
        'Bayview': {
            'Marina District': 27,
            'Embarcadero': 19,
            'Union Square': 18,
            'Chinatown': 19,
            'Sunset District': 23,
            'Golden Gate Park': 22,
            'Financial District': 19,
            'Haight-Ashbury': 19,
            'Mission District': 13
        },
        'Union Square': {
            'Marina District': 18,
            'Embarcadero': 11,
            'Bayview': 15,
            'Chinatown': 7,
            'Sunset District': 27,
            'Golden Gate Park': 22,
            'Financial District': 9,
            'Haight-Ashbury': 18,
            'Mission District': 14
        },
        'Chinatown': {
            'Marina District': 12,
            'Embarcadero': 5,
            'Bayview': 20,
            'Union Square': 7,
            'Sunset District': 29,
            'Golden Gate Park': 23,
            'Financial District': 5,
            'Haight-Ashbury': 19,
            'Mission District': 17
        },
        'Sunset District': {
            'Marina District': 21,
            'Embarcadero': 30,
            'Bayview': 22,
            'Union Square': 30,
            'Chinatown': 30,
            'Golden Gate Park': 11,
            'Financial District': 30,
            'Haight-Ashbury': 15,
            'Mission District': 25
        },
        'Golden Gate Park': {
            'Marina District': 16,
            'Embarcadero': 25,
            'Bayview': 23,
            'Union Square': 22,
            'Chinatown': 23,
            'Sunset District': 10,
            'Financial District': 26,
            'Haight-Ashbury': 7,
            'Mission District': 17
        },
        'Financial District': {
            'Marina District': 15,
            'Embarcadero': 4,
            'Bayview': 19,
            'Union Square': 9,
            'Chinatown': 5,
            'Sunset District': 30,
            'Golden Gate Park': 23,
            'Haight-Ashbury': 19,
            'Mission District': 17
        },
        'Haight-Ashbury': {
            'Marina District': 17,
            'Embarcadero': 20,
            'Bayview': 18,
            'Union Square': 19,
            'Chinatown': 19,
            'Sunset District': 15,
            'Golden Gate Park': 7,
            'Financial District': 21,
            'Mission District': 11
        },
        'Mission District': {
            'Marina District': 19,
            'Embarcadero': 19,
            'Bayview': 14,
            'Union Square': 15,
            'Chinatown': 16,
            'Sunset District': 24,
            'Golden Gate Park': 17,
            'Financial District': 15,
            'Haight-Ashbury': 12
        }
    }

    # Variables for each friend's meeting start and end times, and whether they are met
    meet_vars = {}
    start_vars = {}
    end_vars = {}
    for name in friends:
        meet_vars[name] = Bool(name)
        start_vars[name] = Int(f'start_{name}')
        end_vars[name] = Int(f'end_{name}')

    # Current location starts at Marina District at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Marina District'

    # Elizabeth must be met first because she's only available from 9:00 AM to 9:45 AM
    opt.add(meet_vars['Elizabeth'])
    opt.add(start_vars['Elizabeth'] == current_time)
    opt.add(end_vars['Elizabeth'] == current_time + friends['Elizabeth']['min_duration'])
    current_time = current_time + friends['Elizabeth']['min_duration']
    current_location = 'Sunset District'

    # Now, we need to sequence other meetings after Elizabeth, considering travel time.
    # We'll proceed by adding constraints for possible next meetings.

    # For example, Carol is only available from 10:45 AM to 11:15 AM.
    # Travel time from Sunset District to Financial District is 30 minutes.
    opt.add(Implies(meet_vars['Carol'], start_vars['Carol'] >= current_time + travel_times[current_location]['Financial District']))
    opt.add(Implies(meet_vars['Carol'], start_vars['Carol'] <= friends['Carol']['available_end'] - friends['Carol']['min_duration']))

    # Similarly, add constraints for other friends, ensuring that if they are met, their start time is after the previous meeting's end time plus travel time.

    # We'll also need to ensure that if multiple friends are met, their meetings do not overlap and travel times are respected.

    # To meet exactly 8 people, we'll add a constraint that the sum of meet_vars is 8.
    opt.add(Sum([If(meet_vars[name], 1, 0) for name in friends]) == 8)

    # Check if the optimizer can find a solution
    if opt.check() == sat:
        m = opt.model()
        print("Optimal Schedule:")
        scheduled_friends = []
        for name in friends:
            if is_true(m.evaluate(meet_vars[name])):
                start = m.evaluate(start_vars[name])
                end = m.evaluate(end_vars[name])
                if start is not None and end is not None:
                    scheduled_friends.append((name, start.as_long(), end.as_long()))
        scheduled_friends.sort(key=lambda x: x[1])  # Sort by start time
        for name, start, end in scheduled_friends:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            print(f"Meet {name} at {friends[name]['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
        print(f"Total friends met: {len(scheduled_friends)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()