from itertools import permutations
from z3 import Int, Solver, sat

# Create a solver and add constraints
solver = Solver()
solver.add(Int('s_0_0') == 60)  # Friend 0 in position 0 starts at 60 minutes (1:00)
solver.add(Int('s_1_0') == 90)  # Friend 1 in position 0 starts at 90 minutes (1:30)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()

    # Define friends data
    friends_data = {
        0: {'location': 'A', 'min_duration': 30},
        1: {'location': 'B', 'min_duration': 45}
    }

    friends = list(friends_data.keys())

    # Try all permutations of friends
    for perm in permutations(friends):
        # Initialize itinerary and tracking variables
        itinerary = []
        prev_time = 0
        prev_loc = None

        # Process each friend in the current permutation
        for i, friend in enumerate(perm):
            friend_info = friends_data[friend]
            current_loc = friend_info['location']
            var_name = f's_{friend}_{i}'
            s = model.evaluate(Int(var_name)).as_long()
            end_time = s + friend_info['min_duration']
            start_hm = f"{(s // 60)}:{(s % 60):02d}"
            end_hm = f"{(end_time // 60)}:{(end_time % 60):02d}"

            itinerary.append({
                "action": "meet",
                "location": current_loc,
                "person": friend,
                "start_time": start_hm,
                "end_time": end_hm
            })

            prev_time = end_time
            prev_loc = current_loc

        # Output the itinerary for the current permutation
        print(f"Itinerary for permutation {perm}:")
        for entry in itinerary:
            print(entry)
else:
    print("No solution found.")