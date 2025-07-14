from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Locations and their indices
    locations = {
        'Chinatown': 0,
        'Embarcadero': 1,
        'Pacific Heights': 2,
        'Russian Hill': 3,
        'Haight-Ashbury': 4,
        'Golden Gate Park': 5,
        'Fisherman\'s Wharf': 6,
        'Sunset District': 7,
        'The Castro': 8
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 5, 10, 7, 19, 23, 8, 29, 22],  # Chinatown
        [7, 0, 11, 8, 21, 25, 6, 30, 25],  # Embarcadero
        [11, 10, 0, 7, 11, 15, 13, 21, 16],  # Pacific Heights
        [9, 8, 7, 0, 17, 21, 7, 23, 21],  # Russian Hill
        [19, 20, 12, 17, 0, 7, 23, 15, 6],  # Haight-Ashbury
        [23, 25, 16, 19, 7, 0, 24, 10, 13],  # Golden Gate Park
        [12, 8, 12, 7, 22, 25, 0, 27, 27],  # Fisherman's Wharf
        [30, 30, 21, 24, 15, 11, 29, 0, 17],  # Sunset District
        [22, 22, 16, 18, 6, 11, 24, 17, 0]   # The Castro
    ]

    # Friends' data: name, location, start time, end time, min duration (in minutes)
    friends = [
        ('Richard', 'Embarcadero', 15*60 + 15, 18*60 + 45, 90),
        ('Mark', 'Pacific Heights', 15*60, 17*60, 45),
        ('Matthew', 'Russian Hill', 17*60 + 30, 21*60, 90),
        ('Rebecca', 'Haight-Ashbury', 14*60 + 45, 18*60, 60),
        ('Melissa', 'Golden Gate Park', 13*60 + 45, 17*60 + 30, 90),
        ('Margaret', 'Fisherman\'s Wharf', 14*60 + 45, 20*60 + 15, 15),
        ('Emily', 'Sunset District', 15*60 + 45, 17*60, 45),
        ('George', 'The Castro', 14*60, 16*60 + 15, 75)
    ]

    # Variables for each friend
    met = [Bool(f'met_{name}') for name, _, _, _, _ in friends]
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]

    # Constraints for each friend
    for i, (name, loc, start, end, dur) in enumerate(friends):
        s.add(Implies(met[i], And(
            start_vars[i] >= start,
            end_vars[i] <= end,
            end_vars[i] == start_vars[i] + dur,
            end_vars[i] <= end  # Ensure meeting ends before friend leaves
        )))

    # Initial position: Chinatown at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = locations['Chinatown']

    # Must meet exactly 5 people
    s.add(Sum([If(m, 1, 0) for m in met]) == 5)

    # Order of meetings (select 5 out of 8)
    order = [Int(f'order_{i}') for i in range(5)]
    s.add(Distinct(order))
    for i in range(5):
        s.add(order[i] >= 0)
        s.add(order[i] < len(friends))

    # Sequence variables for the order
    seq_start = [Int(f'seq_start_{i}') for i in range(5)]
    seq_end = [Int(f'seq_end_{i}') for i in range(5)]
    seq_loc = [Int(f'seq_loc_{i}') for i in range(5)]

    # First meeting constraints
    for j in range(len(friends)):
        s.add(Implies(order[0] == j, And(
            seq_start[0] == start_vars[j],
            seq_end[0] == end_vars[j],
            seq_loc[0] == locations[friends[j][1]],
            met[j]
        )))

    # First meeting must start after current_time + travel time
    for loc in range(len(locations)):
        s.add(Implies(seq_loc[0] == loc, 
                     seq_start[0] >= current_time + travel_times[current_loc][loc]))

    # Subsequent meetings
    for i in range(1, 5):
        for j in range(len(friends)):
            s.add(Implies(order[i] == j, And(
                seq_start[i] == start_vars[j],
                seq_end[i] == end_vars[j],
                seq_loc[i] == locations[friends[j][1]],
                met[j]
            )))

        # Start time of current meeting >= end time of previous + travel time
        for prev_loc in range(len(locations)):
            for curr_loc in range(len(locations)):
                s.add(Implies(And(seq_loc[i-1] == prev_loc, seq_loc[i] == curr_loc),
                             seq_start[i] >= seq_end[i-1] + travel_times[prev_loc][curr_loc]))

    # Additional constraints to ensure meeting times are within availability
    # Richard must be met between 15:15 and 18:45
    richard_idx = [i for i, (name, _, _, _, _) in enumerate(friends) if name == 'Richard'][0]
    s.add(Implies(met[richard_idx], And(
        start_vars[richard_idx] >= 15*60 + 15,
        end_vars[richard_idx] <= 18*60 + 45
    )))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Solution found!")
        
        # Print the friends met in order
        met_friends = []
        for i in range(5):
            friend_idx = m.evaluate(order[i]).as_long()
            name = friends[friend_idx][0]
            loc = friends[friend_idx][1]
            start = m.evaluate(start_vars[friend_idx]).as_long()
            end = m.evaluate(end_vars[friend_idx]).as_long()
            met_friends.append((name, loc, start, end))
        
        # Print schedule
        print("Schedule:")
        current_loc = 'Chinatown'
        current_time = 540
        for i, (name, loc, start, end) in enumerate(met_friends):
            travel = travel_times[locations[current_loc]][locations[loc]]
            print(f"{current_time//60:02d}:{current_time%60:02d} - Depart from {current_loc}")
            print(f"Travel time: {travel} minutes")
            print(f"{start//60:02d}:{start%60:02d} - {end//60:02d}:{end%60:02d} - Meet {name} at {loc}")
            current_time = end
            current_loc = loc
        
        print(f"\nTotal friends met: 5")
    else:
        print("No solution found")

solve_scheduling()