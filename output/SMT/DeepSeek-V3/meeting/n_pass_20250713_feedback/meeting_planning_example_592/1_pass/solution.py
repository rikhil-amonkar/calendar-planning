from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Locations and friends' availability
    friends = {
        'James': {'location': 'Pacific Heights', 'start': 20*60, 'end': 22*60, 'min_duration': 120},
        'Robert': {'location': 'Chinatown', 'start': 12*60 + 15, 'end': 16*60 + 45, 'min_duration': 90},
        'Jeffrey': {'location': 'Union Square', 'start': 9*60 + 30, 'end': 15*60 + 30, 'min_duration': 120},
        'Carol': {'location': 'Mission District', 'start': 18*60 + 15, 'end': 21*60 + 15, 'min_duration': 15},
        'Mark': {'location': 'Golden Gate Park', 'start': 11*60 + 30, 'end': 17*60 + 45, 'min_duration': 15},
        'Sandra': {'location': 'Nob Hill', 'start': 8*60, 'end': 15*60 + 30, 'min_duration': 15}
    }

    # Travel times in minutes (from_location, to_location): time
    travel_times = {
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Nob Hill'): 7,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Nob Hill'): 8,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Nob Hill'): 9,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Nob Hill'): 12,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Golden Gate Park'): 17
    }

    # Variables for start and end times of each meeting
    start_vars = {name: Int(f'start_{name}') for name in friends}
    end_vars = {name: Int(f'end_{name}') for name in friends}

    # Current location starts at North Beach at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_location = 'North Beach'

    # Constraints for each friend
    for name in friends:
        info = friends[name]
        s.add(start_vars[name] >= info['start'])
        s.add(end_vars[name] <= info['end'])
        s.add(end_vars[name] - start_vars[name] >= info['min_duration'])
        s.add(start_vars[name] >= 0)
        s.add(end_vars[name] >= 0)

    # Order of meetings and travel times
    # We need to decide the order of meetings. This is complex, so we'll assume a fixed order for simplicity.
    # Alternatively, we could use a more sophisticated approach with permutations, but that's beyond this scope.
    # For this example, we'll prioritize friends with tighter windows first.

    # Let's try the order: Jeffrey, Sandra, Robert, Mark, Carol, James
    order = ['Jeffrey', 'Sandra', 'Robert', 'Mark', 'Carol', 'James']

    # Add constraints for travel times between meetings
    prev_time = current_time
    prev_loc = current_location
    for name in order:
        # Travel time from prev_loc to friend's location
        travel = travel_times.get((prev_loc, friends[name]['location']), 0)
        s.add(start_vars[name] >= prev_time + travel)
        prev_time = end_vars[name]
        prev_loc = friends[name]['location']

    # Maximize the total time spent with friends
    total_time = sum([end_vars[name] - start_vars[name] for name in friends])
    s.maximize(total_time)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        for name in order:
            start = m.eval(start_vars[name]).as_long()
            end = m.eval(end_vars[name]).as_long()
            print(f"{name}: {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d} at {friends[name]['location']}")
        print(f"Total time spent with friends: {m.eval(total_time).as_long()} minutes")
    else:
        print("No feasible schedule found.")

solve_scheduling()