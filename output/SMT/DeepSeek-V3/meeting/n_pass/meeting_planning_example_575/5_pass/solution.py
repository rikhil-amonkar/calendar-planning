from z3 import *

def solve_scheduling():
    s = Solver()

    # Friend data with availability windows and minimum durations
    friends = {
        'Rebecca': {'location': 'Presidio', 'start': 18.25, 'end': 20.75, 'min_duration': 1.0},
        'Linda': {'location': 'Sunset District', 'start': 15.5, 'end': 19.75, 'min_duration': 0.5},
        'Elizabeth': {'location': 'Haight-Ashbury', 'start': 17.25, 'end': 19.5, 'min_duration': 1.75},
        'William': {'location': 'Mission District', 'start': 13.25, 'end': 19.5, 'min_duration': 0.5},
        'Robert': {'location': 'Golden Gate Park', 'start': 14.25, 'end': 21.5, 'min_duration': 0.75},
        'Mark': {'location': 'Russian Hill', 'start': 10.0, 'end': 21.25, 'min_duration': 1.25}
    }

    # Travel times in hours
    travel_times = {
        ('The Castro', 'Presidio'): 20/60,
        ('The Castro', 'Sunset District'): 17/60,
        ('The Castro', 'Haight-Ashbury'): 6/60,
        ('The Castro', 'Mission District'): 7/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('The Castro', 'Russian Hill'): 18/60,
        ('Presidio', 'Sunset District'): 15/60,
        ('Presidio', 'Haight-Ashbury'): 15/60,
        ('Presidio', 'Mission District'): 26/60,
        ('Presidio', 'Golden Gate Park'): 12/60,
        ('Presidio', 'Russian Hill'): 14/60,
        ('Sunset District', 'Haight-Ashbury'): 15/60,
        ('Sunset District', 'Mission District'): 24/60,
        ('Sunset District', 'Golden Gate Park'): 11/60,
        ('Sunset District', 'Russian Hill'): 24/60,
        ('Haight-Ashbury', 'Mission District'): 11/60,
        ('Haight-Ashbury', 'Golden Gate Park'): 7/60,
        ('Haight-Ashbury', 'Russian Hill'): 17/60,
        ('Mission District', 'Golden Gate Park'): 17/60,
        ('Mission District', 'Russian Hill'): 15/60,
        ('Golden Gate Park', 'Russian Hill'): 19/60
    }

    # Create variables
    start_times = {name: Real(f'start_{name}') for name in friends}
    end_times = {name: Real(f'end_{name}') for name in friends}
    meet_order = {name: Int(f'order_{name}') for name in friends}
    prev_location = {name: String(f'prev_loc_{name}') for name in friends}

    # Starting point
    current_time = 9.0  # 9:00 AM
    current_location = 'The Castro'

    # Basic constraints for each friend
    for name in friends:
        # Meeting must be within availability window
        s.add(start_times[name] >= friends[name]['start'])
        s.add(end_times[name] <= friends[name]['end'])
        # Meeting duration must be at least minimum
        s.add(end_times[name] - start_times[name] >= friends[name]['min_duration'])
        # Each friend gets unique order number (1-6)
        s.add(meet_order[name] >= 1, meet_order[name] <= 6)

    # All order numbers must be distinct
    s.add(Distinct([meet_order[name] for name in friends]))

    # Constraints for travel times between meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If meeting name1 comes before name2
                cond = meet_order[name1] < meet_order[name2]
                # Then name2 must start after name1 ends plus travel time
                travel = travel_times.get((friends[name1]['location'], friends[name2]['location']), 0)
                s.add(Implies(cond, start_times[name2] >= end_times[name1] + travel))

    # First meeting must be reachable from starting location
    for name in friends:
        travel = travel_times.get((current_location, friends[name]['location']), 0)
        s.add(Implies(meet_order[name] == 1, start_times[name] >= current_time + travel))

    # Check solution
    if s.check() == sat:
        model = s.model()
        print("SOLUTION:")
        # Sort friends by meeting order
        ordered_friends = sorted(friends.keys(), 
                               key=lambda x: model.evaluate(meet_order[x]).as_long())
        for name in ordered_friends:
            start = model.evaluate(start_times[name])
            end = model.evaluate(end_times[name])
            print(f"Meet {name} at {friends[name]['location']} from {start} to {end}")
    else:
        print("No feasible schedule found.")

solve_scheduling()