from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and friends
    locations = ['Pacific Heights', 'North Beach', 'Financial District', 'Alamo Square', 'Mission District']
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

    # Current location and time tracking variables
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

        # If not meeting the friend, the meeting times are irrelevant (but we set them to 0 for simplicity)
        s.add(Implies(Not(meet_friend[name]), And(
            meeting_start[name] == 0,
            meeting_end[name] == 0
        )))

    # Order of meetings and travel times
    # We'll assume the following order: Kevin -> Helen -> Betty or Amanda
    # This is a heuristic to simplify the problem

    # Kevin's meeting
    s.add(Implies(meet_friend['Kevin'], And(
        meeting_start['Kevin'] >= current_time + travel_times[current_location]['Mission District'],
        meeting_start['Kevin'] >= friends['Kevin']['start'],
        meeting_end['Kevin'] == meeting_start['Kevin'] + friends['Kevin']['duration'],
        meeting_end['Kevin'] <= friends['Kevin']['end']
    )))

    # After Kevin, travel to Helen's location
    s.add(Implies(And(meet_friend['Kevin'], meet_friend['Helen']), And(
        meeting_start['Helen'] >= meeting_end['Kevin'] + travel_times['Mission District']['North Beach'],
        meeting_start['Helen'] >= friends['Helen']['start'],
        meeting_end['Helen'] == meeting_start['Helen'] + friends['Helen']['duration'],
        meeting_end['Helen'] <= friends['Helen']['end']
    )))

    # After Helen, travel to Betty or Amanda
    # Betty's meeting
    s.add(Implies(And(meet_friend['Helen'], meet_friend['Betty']), And(
        meeting_start['Betty'] >= meeting_end['Helen'] + travel_times['North Beach']['Financial District'],
        meeting_start['Betty'] >= friends['Betty']['start'],
        meeting_end['Betty'] == meeting_start['Betty'] + friends['Betty']['duration'],
        meeting_end['Betty'] <= friends['Betty']['end']
    )))

    # Amanda's meeting
    s.add(Implies(And(meet_friend['Helen'], meet_friend['Amanda']), And(
        meeting_start['Amanda'] >= meeting_end['Helen'] + travel_times['North Beach']['Alamo Square'],
        meeting_start['Amanda'] >= friends['Amanda']['start'],
        meeting_end['Amanda'] == meeting_start['Amanda'] + friends['Amanda']['duration'],
        meeting_end['Amanda'] <= friends['Amanda']['end']
    )))

    # Cannot meet both Betty and Amanda due to time constraints
    s.add(Or(Not(meet_friend['Betty']), Not(meet_friend['Amanda'])))

    # Maximize the number of friends met
    # We'll use a binary search approach to find the maximum number of friends that can be met
    max_friends = 0
    optimal_schedule = None

    for num_friends in range(len(friends), 0, -1):
        s.push()
        s.add(Sum([If(meet_friend[name], 1, 0) for name in friends]) >= num_friends)
        if s.check() == sat:
            m = s.model()
            max_friends = num_friends
            optimal_schedule = m
            break
        s.pop()

    if optimal_schedule is not None:
        print(f"Optimal schedule meets {max_friends} friends:")
        for name in friends:
            if optimal_schedule.evaluate(meet_friend[name]):
                start = optimal_schedule.evaluate(meeting_start[name])
                end = optimal_schedule.evaluate(meeting_end[name])
                print(f"Meet {name} at {friends[name]['location']} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()