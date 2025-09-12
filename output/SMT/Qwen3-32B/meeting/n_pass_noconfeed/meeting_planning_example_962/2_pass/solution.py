# Precompute travel times between friends
friend_locations = [f['location'] for f in friends]
num_friends = len(friends)
travel_time_between = [[0] * num_friends for _ in range(num_friends)]
for j in range(num_friends):
    for k in range(num_friends):
        loc_j = friend_locations[j]
        loc_k = friend_locations[k]
        if loc_j == loc_k:
            travel_time_between[j][k] = 0
        else:
            travel_time_between[j][k] = travel_times[loc_j][loc_k]