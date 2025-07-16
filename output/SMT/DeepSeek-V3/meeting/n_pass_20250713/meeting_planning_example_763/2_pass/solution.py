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

    # Variables for each friend: whether they are met, start and end times of the meeting
    met = [Bool(f'met_{name}') for name, _, _, _, _ in friends]
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]

    # Constraints for each friend
    for i, (name, loc, start, end, dur) in enumerate(friends):
        loc_idx = locations[loc]
        s.add(Implies(met[i], start_vars[i] >= start))
        s.add(Implies(met[i], end_vars[i] <= end))
        s.add(Implies(met[i], end_vars[i] == start_vars[i] + dur))

    # Initial position: Chinatown at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = locations['Chinatown']

    # We need to meet exactly 5 people
    s.add(Sum([If(m, 1, 0) for m in met]) == 5)

    # Order of meetings (permutation of the friends)
    order = [Int(f'order_{i}') for i in range(5)]
    s.add(Distinct(order))
    for i in range(5):
        s.add(order[i] >= 0)
        s.add(order[i] < len(friends))

    # Sequence variables for the order
    seq_start = [Int(f'seq_start_{i}') for i in range(5)]
    seq_end = [Int(f'seq_end_{i}') for i in range(5)]
    seq_loc = [Int(f'seq_loc_{i}') for i in range(5)]

    # Helper function to get travel time between two locations
    def get_travel_time(from_loc, to_loc):
        return travel_times[from_loc][to_loc]

    # First meeting
    for j in range(len(friends)):
        s.add(Implies(order[0] == j, seq_start[0] == start_vars[j]))
        s.add(Implies(order[0] == j, seq_end[0] == end_vars[j]))
        s.add(Implies(order[0] == j, seq_loc[0] == locations[friends[j][1]]))
        s.add(Implies(order[0] == j, met[j]))

    # First meeting must start after current_time + travel time
    s.add(seq_start[0] >= current_time + get_travel_time(current_loc, seq_loc[0]))

    # Subsequent meetings
    for i in range(1, 5):
        for j in range(len(friends)):
            s.add(Implies(order[i] == j, seq_start[i] == start_vars[j]))
            s.add(Implies(order[i] == j, seq_end[i] == end_vars[j]))
            s.add(Implies(order[i] == j, seq_loc[i] == locations[friends[j][1]]))
            s.add(Implies(order[i] == j, met[j]))

        # Start time of current meeting >= end time of previous + travel time
        s.add(seq_start[i] >= seq_end[i-1] + get_travel_time(seq_loc[i-1], seq_loc[i]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Solution found!")
        # Print the order of meetings
        order_sol = [m.evaluate(order[i]) for i in range(5)]
        print("Order of meetings:", order_sol)
        # Print the friends met
        for i in range(len(friends)):
            if m.evaluate(met[i]):
                print(f"Meet {friends[i][0]} at {friends[i][1]} from {m.evaluate(start_vars[i])} to {m.evaluate(end_vars[i])}")
        # Print the total number of friends met
        print("Total friends met:", sum(1 for i in range(len(friends)) if m.evaluate(met[i]) else 0))
    else:
        print("No solution found")

solve_scheduling()