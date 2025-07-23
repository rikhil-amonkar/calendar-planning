from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their locations, availability, and desired meeting durations
    friends = {
        'Betty': {'location': 'Russian Hill', 'start': 7*60, 'end': 16*60 + 45, 'duration': 105},
        'Melissa': {'location': 'Alamo Square', 'start': 9*60 + 30, 'end': 17*60 + 15, 'duration': 105},
        'Joshua': {'location': 'Haight-Ashbury', 'start': 12*60 + 15, 'end': 19*60, 'duration': 90},
        'Jeffrey': {'location': 'Marina District', 'start': 12*60 + 15, 'end': 18*60, 'duration': 45},
        'James': {'location': 'Bayview', 'start': 7*60 + 30, 'end': 20*60, 'duration': 90},
        'Anthony': {'location': 'Chinatown', 'start': 11*60 + 45, 'end': 13*60 + 30, 'duration': 75},
        'Timothy': {'location': 'Presidio', 'start': 12*60 + 30, 'end': 14*60 + 45, 'duration': 90},
        'Emily': {'location': 'Sunset District', 'start': 19*60 + 30, 'end': 21*60 + 30, 'duration': 120}
    }

    # Define travel times (in minutes) between locations
    travel_times = {
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Sunset District'): 27,
        ('Russian Hill', 'Union Square'): 10,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Sunset District'): 16,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Sunset District'): 19,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Sunset District'): 23,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Sunset District'): 29,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Presidio'): 16
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Current location starts at Union Square at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Union Square'

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        start_available = friend['start']
        end_available = friend['end']
        duration = friend['duration']
        start_var = meeting_vars[name]['start']
        end_var = meeting_vars[name]['end']
        met_var = meeting_vars[name]['met']

        # If meeting the friend, constraints on start and end times
        s.add(Implies(met_var, start_var >= start_available))
        s.add(Implies(met_var, end_var <= end_available))
        s.add(Implies(met_var, end_var == start_var + duration))

        # Travel time from current location to friend's location
        travel_time = travel_times.get((current_location, loc), 0)
        s.add(Implies(met_var, start_var >= current_time + travel_time))

        # Update current_time and current_location if meeting this friend
        current_time = If(met_var, end_var, current_time)
        current_location = If(met_var, loc, current_location)

    # Ensure meeting Emily is last (since she's available in the evening)
    emily_met = meeting_vars['Emily']['met']
    for name in friends:
        if name != 'Emily':
            s.add(Implies(meeting_vars[name]['met'], meeting_vars[name]['end'] <= meeting_vars['Emily']['start']))

    # Maximize the number of friends met
    total_met = Sum([If(meeting_vars[name]['met'], 1, 0) for name in friends])
    s.maximize(total_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        schedule = []
        for name in friends:
            if m.evaluate(meeting_vars[name]['met']):
                start = m.evaluate(meeting_vars[name]['start']).as_long()
                end = m.evaluate(meeting_vars[name]['end']).as_long()
                start_time = f"{start // 60}:{start % 60:02d}"
                end_time = f"{end // 60}:{end % 60:02d}"
                schedule.append((name, friends[name]['location'], start_time, end_time))
        # Sort by start time
        schedule.sort(key=lambda x: int(x[2].split(':')[0]) * 60 + int(x[2].split(':')[1]))
        for entry in schedule:
            print(f"Meet {entry[0]} at {entry[1]} from {entry[2]} to {entry[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()