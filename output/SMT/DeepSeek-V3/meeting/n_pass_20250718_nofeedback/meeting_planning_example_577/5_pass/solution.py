from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and travel times
    locations = {
        'Haight-Ashbury': 0,
        'Russian Hill': 1,
        'Fisherman\'s Wharf': 2,
        'Nob Hill': 3,
        'Golden Gate Park': 4,
        'Alamo Square': 5,
        'Pacific Heights': 6
    }

    travel_times = [
        [0, 17, 23, 15, 7, 5, 12],    # Haight-Ashbury
        [17, 0, 7, 5, 21, 15, 7],      # Russian Hill
        [22, 7, 0, 11, 25, 20, 12],    # Fisherman's Wharf
        [13, 5, 11, 0, 17, 11, 8],     # Nob Hill
        [7, 19, 24, 20, 0, 10, 16],    # Golden Gate Park
        [5, 13, 19, 11, 9, 0, 10],     # Alamo Square
        [11, 7, 13, 8, 15, 10, 0]      # Pacific Heights
    ]

    # Friends' data: name, location, start_available, end_available, min_duration
    friends = [
        ('Stephanie', 'Russian Hill', 20*60, 20*60 + 45, 15),
        ('Kevin', 'Fisherman\'s Wharf', 19*60 + 15, 21*60 + 45, 75),
        ('Robert', 'Nob Hill', 7*60 + 45, 10*60 + 30, 90),
        ('Steven', 'Golden Gate Park', 8*60 + 30, 17*60, 75),
        ('Anthony', 'Alamo Square', 7*60 + 45, 19*60 + 45, 15),
        ('Sandra', 'Pacific Heights', 14*60 + 45, 21*60 + 45, 45)
    ]

    # Current location starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = 9 * 60
    current_loc = locations['Haight-Ashbury']

    # Variables for each meeting: start, end
    meet_vars = []
    for name, loc, start_avail, end_avail, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meet_vars.append((name, loc, start, end, start_avail, end_avail, min_dur))
        s.add(start >= start_avail)
        s.add(end <= end_avail)
        s.add(end - start >= min_dur)
        s.add(start >= 0)
        s.add(end >= 0)

    # Create a binary variable for each pair indicating if i comes before j
    before = [[Bool(f'before_{i}_{j}') for j in range(len(friends))] for i in range(len(friends))]

    # Ordering constraints
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # Either i comes before j or j comes before i
                s.add(Or(before[i][j], before[j][i]))
                # Transitivity
                for k in range(len(friends)):
                    if i != k and j != k:
                        s.add(Implies(And(before[i][j], before[j][k]), before[i][k]))

    # Travel time constraints
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                i_name, i_loc, i_start, i_end, _, _, _ = meet_vars[i]
                j_name, j_loc, j_start, j_end, _, _, _ = meet_vars[j]
                travel_time = travel_times[locations[i_loc]][locations[j_loc]]
                s.add(Implies(before[i][j], j_start >= i_end + travel_time))

    # First meeting must be after current time + travel time
    for i in range(len(friends)):
        i_name, i_loc, i_start, i_end, _, _, _ = meet_vars[i]
        travel_time = travel_times[current_loc][locations[i_loc]]
        # If this is the first meeting (no one comes before it)
        s.add(Implies(And([Not(before[j][i]) for j in range(len(friends)) if j != i]), 
                     i_start >= current_time + travel_time))

    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        # Determine the order
        order = []
        for i in range(len(friends)):
            # Count how many meetings come before this one
            before_count = sum(1 for j in range(len(friends)) 
                             if i != j and is_true(m.evaluate(before[j][i])))
            order.append((before_count, i))
        # Sort by before_count to get the actual order
        order_sorted = sorted(order, key=lambda x: x[0])
        itinerary = []
        for _, idx in order_sorted:
            name, loc, start, end, _, _, _ = meet_vars[idx]
            start_val = m.evaluate(start).as_long()
            end_val = m.evaluate(end).as_long()
            start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time = f"{end_val // 60:02d}:{end_val % 60:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver
result = solve_scheduling()
print(json.dumps(result, indent=2))