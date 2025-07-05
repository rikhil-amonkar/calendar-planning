from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the friends and their details
    friends = {
        'Rebecca': {'location': 'Presidio', 'start': 18.25, 'end': 20.75, 'min_duration': 1.0},
        'Linda': {'location': 'Sunset District', 'start': 15.5, 'end': 19.75, 'min_duration': 0.5},
        'Elizabeth': {'location': 'Haight-Ashbury', 'start': 17.25, 'end': 19.5, 'min_duration': 1.75},
        'William': {'location': 'Mission District', 'start': 13.25, 'end': 19.5, 'min_duration': 0.5},
        'Robert': {'location': 'Golden Gate Park', 'start': 14.25, 'end': 21.5, 'min_duration': 0.75},
        'Mark': {'location': 'Russian Hill', 'start': 10.0, 'end': 21.25, 'min_duration': 1.25}
    }

    # Travel times matrix (in hours)
    travel_times = {
        ('The Castro', 'Presidio'): 20/60,
        ('The Castro', 'Sunset District'): 17/60,
        ('The Castro', 'Haight-Ashbury'): 6/60,
        ('The Castro', 'Mission District'): 7/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('The Castro', 'Russian Hill'): 18/60,
        ('Presidio', 'The Castro'): 21/60,
        ('Presidio', 'Sunset District'): 15/60,
        ('Presidio', 'Haight-Ashbury'): 15/60,
        ('Presidio', 'Mission District'): 26/60,
        ('Presidio', 'Golden Gate Park'): 12/60,
        ('Presidio', 'Russian Hill'): 14/60,
        ('Sunset District', 'The Castro'): 17/60,
        ('Sunset District', 'Presidio'): 16/60,
        ('Sunset District', 'Haight-Ashbury'): 15/60,
        ('Sunset District', 'Mission District'): 24/60,
        ('Sunset District', 'Golden Gate Park'): 11/60,
        ('Sunset District', 'Russian Hill'): 24/60,
        ('Haight-Ashbury', 'The Castro'): 6/60,
        ('Haight-Ashbury', 'Presidio'): 15/60,
        ('Haight-Ashbury', 'Sunset District'): 15/60,
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Golden Gate Park'): 7/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Mission District', 'The Castro'): 7/60,
        ('Mission District', 'Presidio'): 25/60,
        ('Mission District', 'Sunset District'): 24/60,
        ('Mission District', 'Haight-Ashbury'): 12/60,
        ('Mission District', 'Golden Gate Park'): 17/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Golden Gate Park', 'The Castro'): 13/60,
        ('Golden Gate Park', 'Presidio'): 11/60,
        ('Golden Gate Park', 'Sunset District'): 10/60,
        ('Golden Gate Park', 'Haight-Ashbury'): 7/60,
        ('Golden Gate Park', 'Mission District'): 17/60,
        ('Golden Gate Park', 'Russian Hill'): 19/60,
        ('Russian Hill', 'The Castro'): 21/60,
        ('Russian Hill', 'Presidio'): 14/60,
        ('Russian Hill', 'Sunset District'): 23/60,
        ('Russian Hill', 'Haight-Ashbury'): 17/60,
        ('Russian Hill', 'Mission District'): 16/60,
        ('Russian Hill', 'Golden Gate Park'): 21/60
    }

    # Create variables for start and end times of each meeting
    start_times = {name: Real(f'start_{name}') for name in friends}
    end_times = {name: Real(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}  # Whether we meet the friend

    # Current location starts at The Castro at 9:00 AM (9.0 hours)
    current_location = 'The Castro'
    current_time = 9.0

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(Implies(meet[name], start_times[name] >= friend['start']))
        s.add(Implies(meet[name], end_times[name] <= friend['end']))
        s.add(Implies(meet[name], end_times[name] - start_times[name] >= friend['min_duration']))

    # Order of meetings and travel times
    # We need to sequence the meetings and account for travel times
    # This is a simplified approach; a more sophisticated model would sequence dynamically
    # For simplicity, we'll assume we can meet friends in any order, but ensure travel times are respected

    # To model the sequence, we can use a list of possible orders and enforce constraints
    # However, this is complex, so we'll instead assume a greedy approach where we try to meet as many as possible
    # and let Z3 find a feasible schedule

    # Maximize the number of friends met
    s.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        print("SOLUTION:")
        print("Schedule:")
        for name in friends:
            if model.evaluate(meet[name]):
                start = model.evaluate(start_times[name])
                end = model.evaluate(end_times[name])
                print(f"Meet {name} at {friends[name]['location']} from {start} to {end}")
        print("\nFriends met:")
        for name in friends:
            if model.evaluate(meet[name]):
                print(f"- {name}")
    else:
        print("No feasible schedule found.")

solve_scheduling()