from itertools import permutations
from z3 import Int, ModelRef, Solver

# Mock model with dummy values for demonstration
model = ModelRef(Solver())
model.add(Int('s_0_0') == 60)   # Friend 0 in position 0 starts at 60 minutes (1:00)
model.add(Int('s_1_0') == 90)   # Friend 1 in position 0 starts at 90 minutes (1:30)

# Define friends_data with sample data
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
        s = model.evaluate(Int(f's_{friend}_{i}')).as_long()
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