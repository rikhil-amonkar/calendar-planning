from z3 import *

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Friends' availability and constraints
    friends = {
        'Stephanie': {'location': 'Russian Hill', 'start': time_to_minutes(20, 0), 'end': time_to_minutes(20, 45), 'duration': 15},
        'Kevin': {'location': 'Fisherman\'s Wharf', 'start': time_to_minutes(19, 15), 'end': time_to_minutes(21, 45), 'duration': 75},
        'Robert': {'location': 'Nob Hill', 'start': time_to_minutes(7, 45), 'end': time_to_minutes(10, 30), 'duration': 90},
        'Steven': {'location': 'Golden Gate Park', 'start': time_to_minutes(8, 30), 'end': time_to_minutes(17, 0), 'duration': 75},
        'Anthony': {'location': 'Alamo Square', 'start': time_to_minutes(7, 45), 'end': time_to_minutes(19, 45), 'duration': 15},
        'Sandra': {'location': 'Pacific Heights', 'start': time_to_minutes(14, 45), 'end': time_to_minutes(21, 45), 'duration': 45}
    }

    # Travel times dictionary (simplified for access)
    travel_times = {
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Russian Hill'): 7,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Alamo Square'): 10
    }

    # Create variables for each friend's meeting start time
    start_vars = {}
    for name in friends:
        start_vars[name] = Int(f'start_{name}')

    # Constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        s.add(start_vars[name] >= friend['start'])
        s.add(start_vars[name] + friend['duration'] <= friend['end'])

    # Initial location is Haight-Ashbury at time 0 (9:00 AM)
    current_location = 'Haight-Ashbury'
    current_time = 0

    # Order of meeting friends (we'll try to meet as many as possible)
    # We'll prioritize friends with tighter time windows first
    friend_order = ['Robert', 'Anthony', 'Steven', 'Sandra', 'Kevin', 'Stephanie']

    # Variables to track whether a friend is met
    met = {name: Bool(f'met_{name}') for name in friends}

    # Constraints to ensure meetings are scheduled in order with travel times
    prev_time = current_time
    prev_location = current_location
    for name in friend_order:
        friend = friends[name]
        location = friend['location']
        travel_time = travel_times.get((prev_location, location), 0)
        # If we decide to meet this friend, their start time must be >= prev_time + travel_time
        s.add(Implies(met[name], start_vars[name] >= prev_time + travel_time))
        # Update prev_time and prev_location if meeting this friend
        new_time = If(met[name], start_vars[name] + friend['duration'], prev_time)
        new_location = If(met[name], location, prev_location)
        prev_time = new_time
        prev_location = new_location

    # Maximize the number of friends met
    s.maximize(Sum([If(met[name], 1, 0) for name in friends]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled_friends = []
        for name in sorted(friends.keys(), key=lambda x: m.evaluate(start_vars[x]).as_long() if m.evaluate(met[x]) else float('inf')):
            if m.evaluate(met[name]):
                start = m.evaluate(start_vars[name]).as_long()
                h = (start + 540) // 60
                mnt = (start + 540) % 60
                print(f"Meet {name} at {friends[name]['location']} from {h:02d}:{mnt:02d} to {h:02d}:{(mnt + friends[name]['duration']):02d}")
                scheduled_friends.append(name)
        print(f"Total friends met: {len(scheduled_friends)}")
    else:
        print("No feasible schedule found.")

solve_scheduling_problem()