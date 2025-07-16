from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define locations and friends
    friends = {
        'Helen': {'location': 'North Beach', 'start': 9*60, 'end': 17*60, 'duration': 15},
        'Betty': {'location': 'Financial District', 'start': 19*60, 'end': 21*60 + 45, 'duration': 90},
        'Amanda': {'location': 'Alamo Square', 'start': 19*60 + 45, 'end': 21*60, 'duration': 60},
        'Kevin': {'location': 'Mission District', 'start': 10*60 + 45, 'end': 14*60 + 45, 'duration': 45}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Pacific Heights': {
            'North Beach': 9,
            'Financial District': 13,
            'Alamo Square': 10,
            'Mission District': 15
        },
        'North Beach': {
            'Pacific Heights': 8,
            'Financial District': 8,
            'Alamo Square': 16,
            'Mission District': 18
        },
        'Financial District': {
            'Pacific Heights': 13,
            'North Beach': 7,
            'Alamo Square': 17,
            'Mission District': 17
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'North Beach': 15,
            'Financial District': 17,
            'Mission District': 10
        },
        'Mission District': {
            'Pacific Heights': 16,
            'North Beach': 17,
            'Financial District': 17,
            'Alamo Square': 11
        }
    }

    # Variables for each friend's meeting start and end times
    meeting_start = {name: Int(f'start_{name}') for name in friends}
    meeting_end = {name: Int(f'end_{name}') for name in friends}

    # Variables to indicate whether a friend is met
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # Current location and time
    current_location = 'Pacific Heights'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        duration = friend['duration']
        start_window = friend['start']
        end_window = friend['end']

        # If meeting the friend, the meeting must be within their window and last at least the required duration
        s.add(Implies(meet_friend[name], And(
            meeting_start[name] >= start_window,
            meeting_end[name] <= end_window,
            meeting_end[name] == meeting_start[name] + duration
        )))

        # If not meeting the friend, the meeting times are irrelevant (set to 0)
        s.add(Implies(Not(meet_friend[name]), And(
            meeting_start[name] == 0,
            meeting_end[name] == 0
        )))

    # Kevin must be met first if meeting him
    s.add(Implies(meet_friend['Kevin'], 
          meeting_start['Kevin'] >= current_time + travel_times[current_location]['Mission District']))

    # Helen can be met after Kevin
    s.add(Implies(And(meet_friend['Kevin'], meet_friend['Helen']),
          meeting_start['Helen'] >= meeting_end['Kevin'] + travel_times['Mission District']['North Beach']))

    # Betty can be met after Helen
    s.add(Implies(And(meet_friend['Helen'], meet_friend['Betty']),
          meeting_start['Betty'] >= meeting_end['Helen'] + travel_times['North Beach']['Financial District']))

    # Amanda can be met after Helen
    s.add(Implies(And(meet_friend['Helen'], meet_friend['Amanda']),
          meeting_start['Amanda'] >= meeting_end['Helen'] + travel_times['North Beach']['Alamo Square']))

    # Cannot meet both Betty and Amanda
    s.add(Or(Not(meet_friend['Betty']), Not(meet_friend['Amanda'])))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(meet_friend[name], 1, 0) for name in friends]))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        met_friends = [name for name in friends if is_true(m.evaluate(meet_friend[name]))]
        print(f"Optimal schedule meets {len(met_friends)} friends:")
        for name in met_friends:
            start = m.evaluate(meeting_start[name]).as_long()
            end = m.evaluate(meeting_end[name]).as_long()
            print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No feasible schedule found")

solve_scheduling()