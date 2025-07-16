from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Locations and their indices
    locations = {
        'Pacific Heights': 0,
        'Golden Gate Park': 1,
        'The Castro': 2,
        'Bayview': 3,
        'Marina District': 4,
        'Union Square': 5,
        'Sunset District': 6,
        'Alamo Square': 7,
        'Financial District': 8,
        'Mission District': 9
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 15, 16, 22, 6, 12, 21, 10, 13, 15],  # Pacific Heights
        [16, 0, 13, 23, 16, 22, 10, 9, 26, 17],   # Golden Gate Park
        [16, 11, 0, 19, 21, 19, 17, 8, 21, 7],     # The Castro
        [23, 22, 19, 0, 27, 18, 23, 16, 19, 13],   # Bayview
        [7, 18, 22, 27, 0, 16, 19, 15, 17, 20],    # Marina District
        [15, 22, 17, 15, 18, 0, 27, 15, 9, 14],    # Union Square
        [21, 11, 17, 22, 21, 30, 0, 17, 30, 25],   # Sunset District
        [10, 9, 8, 16, 15, 14, 16, 0, 17, 10],     # Alamo Square
        [13, 23, 20, 19, 15, 9, 30, 17, 0, 17],    # Financial District
        [16, 17, 7, 14, 19, 15, 24, 11, 15, 0]     # Mission District
    ]

    # Friends' data: name, location, start_available, end_available, min_duration (minutes)
    friends = [
        ('Helen', 'Golden Gate Park', 9*60 + 30, 12*60 + 15, 45),
        ('Steven', 'The Castro', 20*60 + 15, 22*60 + 0, 105),
        ('Deborah', 'Bayview', 8*60 + 30, 12*60 + 0, 30),
        ('Matthew', 'Marina District', 9*60 + 15, 14*60 + 15, 45),
        ('Joseph', 'Union Square', 14*60 + 15, 18*60 + 45, 120),
        ('Ronald', 'Sunset District', 16*60 + 0, 20*60 + 45, 60),
        ('Robert', 'Alamo Square', 18*60 + 30, 21*60 + 15, 120),
        ('Rebecca', 'Financial District', 14*60 + 45, 16*60 + 15, 30),
        ('Elizabeth', 'Mission District', 18*60 + 30, 21*60 + 0, 120)
    ]

    # Variables for each friend: start and end times
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    met_vars = [Bool(f'met_{name}') for name, _, _, _, _ in friends]

    # Initial constraints: arrival at Pacific Heights at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = locations['Pacific Heights']

    # Constraints for each friend
    for i, (name, loc, start_avail, end_avail, min_dur) in enumerate(friends):
        loc_idx = locations[loc]

        # If meeting the friend, their start and end must be within availability
        s.add(Implies(met_vars[i], start_vars[i] >= start_avail))
        s.add(Implies(met_vars[i], end_vars[i] <= end_avail))
        s.add(Implies(met_vars[i], end_vars[i] == start_vars[i] + min_dur))

    # Sequence constraints: order of meetings and travel times
    # We need to model the sequence in which friends are met.
    # This is complex, so we'll use a simplified approach where the order is determined by the solver.
    # We'll use a list to represent the order and add constraints accordingly.

    # To simplify, we'll assume that the order is a permutation of friends, and we'll use auxiliary variables.
    # However, this is complex to model directly in Z3 for large instances. Instead, we'll use a greedy approach or prioritize certain friends.

    # For the sake of this problem, we'll prioritize friends with tighter windows and higher durations.

    # We'll create a list of possible orders and check feasibility. But given time, we'll proceed with a simplified model.

    # We'll assume that the order is fixed based on earliest possible meeting times, but this may not be optimal.

    # Alternatively, we can use a greedy approach in the solver by adding constraints that enforce the sequence.

    # For now, let's proceed with a simplified model where we assume that the solver can find a feasible sequence.

    # We'll add constraints that for any two friends met, their meetings do not overlap and travel time is accounted for.
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If both are met, then either i comes before j or vice versa, with travel time
                i_loc = locations[friends[i][1]]
                j_loc = locations[friends[j][1]]
                travel = travel_times[i_loc][j_loc]

                # i before j
                before = And(
                    met_vars[i],
                    met_vars[j],
                    end_vars[i] + travel <= start_vars[j]
                )
                # j before i
                after = And(
                    met_vars[i],
                    met_vars[j],
                    end_vars[j] + travel_times[j_loc][i_loc] <= start_vars[i]
                )
                s.add(Or(Not(met_vars[i]), Not(met_vars[j]), before, after))

    # Also, the first meeting must start after current_time + travel to the location
    for i in range(len(friends)):
        loc_idx = locations[friends[i][1]]
        travel = travel_times[current_location][loc_idx]
        s.add(Implies(met_vars[i], start_vars[i] >= current_time + travel))

    # Maximize the number of friends met
    total_met = Sum([If(met_vars[i], 1, 0) for i in range(len(friends))])
    s.maximize(total_met)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        met_count = 0
        schedule = []
        for i in range(len(friends)):
            if m.evaluate(met_vars[i]):
                met_count += 1
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                start_h = start // 60
                start_m = start % 60
                end_h = end // 60
                end_m = end % 60
                schedule.append((
                    friends[i][0],
                    friends[i][1],
                    f"{start_h}:{start_m:02d}",
                    f"{end_h}:{end_m:02d}"
                ))
        schedule.sort(key=lambda x: int(x[2].split(':')[0]) * 60 + int(x[2].split(':')[1]))
        print(f"Met {met_count} friends:")
        for meet in schedule:
            print(f"Meet {meet[0]} at {meet[1]} from {meet[2]} to {meet[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()