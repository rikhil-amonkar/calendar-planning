from itertools import permutations

# Example: friends_data could be a dictionary of friend info
# e.g., friends_data = {0: {'location': 'A', 'min_duration': 30}, 1: {...}, ...}
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

    # At this point, `itinerary` contains a full schedule for the current permutation
    # You can evaluate or store it as needed