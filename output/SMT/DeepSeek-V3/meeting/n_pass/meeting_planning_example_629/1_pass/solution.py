from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations and friends' data
    friends = {
        'Matthew': {'location': 'Presidio', 'start': 11*60, 'end': 21*60, 'min_duration': 90},
        'Margaret': {'location': 'Chinatown', 'start': 9*60+15, 'end': 18*60+45, 'min_duration': 90},
        'Nancy': {'location': 'Pacific Heights', 'start': 14*60+15, 'end': 17*60, 'min_duration': 15},
        'Helen': {'location': 'Richmond District', 'start': 19*60+45, 'end': 22*60, 'min_duration': 60},
        'Rebecca': {'location': 'Fisherman\'s Wharf', 'start': 21*60+15, 'end': 22*60+15, 'min_duration': 60},
        'Kimberly': {'location': 'Golden Gate Park', 'start': 13*60, 'end': 16*60+30, 'min_duration': 120},
        'Kenneth': {'location': 'Bayview', 'start': 14*60+30, 'end': 18*60, 'min_duration': 60}
    }

    # Travel times (in minutes) between locations. Keys are (from, to).
    travel_times = {
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Bayview'): 23,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Bayview'): 31,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Bayview'): 22,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Bayview'): 22,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Golden Gate Park'): 22
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = (start_var, end_var)
        s.add(start_var >= friends[name]['start'])
        s.add(end_var <= friends[name]['end'])
        s.add(end_var - start_var >= friends[name]['min_duration'])

    # Variables to indicate whether a friend is met
    meet_friend = {name: Bool(f'meet_{name}') for name in friends}

    # Initial location is Russian Hill at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Russian Hill'

    # Sequence of meetings: we need to decide the order in which to meet friends
    # To model this, we'll create a sequence where each step is a decision to meet a friend or not
    # and ensure that travel times are respected between consecutive meetings.

    # We'll use a list to represent the order of meetings, but since the order is not fixed,
    # we'll need to model all possible sequences. This is complex, so instead, we'll
    # use a more straightforward approach by assuming a certain order and checking feasibility.

    # For simplicity, let's assume we can meet friends in any order, but we'll need to ensure
    # that the schedule respects travel times and time windows.

    # We'll create a list of all possible friends to meet and try to find a feasible order.
    # However, this is computationally intensive, so we'll use a heuristic or prioritize friends
    # with tighter time windows.

    # Alternatively, we can model the problem as a disjunction of possible sequences, but this is complex.

    # Instead, we'll use a more practical approach: prioritize friends with the earliest availability
    # and ensure that the schedule is feasible.

    # Let's create a list of friends sorted by their availability start time.
    sorted_friends = sorted(friends.keys(), key=lambda x: friends[x]['start'])

    # We'll create variables for the arrival time at each friend's location.
    arrival_time = {name: Int(f'arrival_{name}') for name in friends}
    departure_time = {name: Int(f'departure_{name}') for name in friends}

    # Initial arrival time at Russian Hill is 540 (9:00 AM)
    prev_time = 540
    prev_location = 'Russian Hill'

    # For each friend, if we decide to meet them, their arrival time must be >= prev_time + travel time
    # and their meeting must fit within their availability.
    for name in sorted_friends:
        loc = friends[name]['location']
        travel_time = travel_times[(prev_location, loc)]
        s.add(Implies(meet_friend[name], arrival_time[name] >= prev_time + travel_time))
        s.add(Implies(meet_friend[name], arrival_time[name] >= friends[name]['start']))
        s.add(Implies(meet_friend[name], meeting_vars[name][0] == arrival_time[name]))
        s.add(Implies(meet_friend[name], meeting_vars[name][1] <= friends[name]['end']))
        s.add(Implies(meet_friend[name], meeting_vars[name][1] - meeting_vars[name][0] >= friends[name]['min_duration']))

        # Update prev_time and prev_location if we meet this friend
        new_prev_time = If(meet_friend[name], meeting_vars[name][1], prev_time)
        new_prev_location = If(meet_friend[name], loc, prev_location)
        prev_time = new_prev_time
        prev_location = new_prev_location

    # Ensure that we don't exceed the time constraints for the last friend
    # For example, Rebecca's meeting must end by 22:15 (1335 minutes)
    # But since the last meeting is Helen or Rebecca, we need to ensure that the schedule fits.

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_friend[name], 1, 0) for name in friends]))

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        total_friends_met = 0
        schedule = []
        for name in sorted_friends:
            if m.evaluate(meet_friend[name]):
                start = m.evaluate(meeting_vars[name][0]).as_long()
                end = m.evaluate(meeting_vars[name][1]).as_long()
                duration = end - start
                start_time = f"{start//60:02d}:{start%60:02d}"
                end_time = f"{end//60:02d}:{end%60:02d}"
                print(f"Meet {name} at {friends[name]['location']} from {start_time} to {end_time} (Duration: {duration} minutes)")
                total_friends_met += 1
                schedule.append((name, friends[name]['location'], start, end))
        print(f"Total friends met: {total_friends_met}")
        return schedule
    else:
        print("No feasible schedule found.")
        return None

solve_scheduling()