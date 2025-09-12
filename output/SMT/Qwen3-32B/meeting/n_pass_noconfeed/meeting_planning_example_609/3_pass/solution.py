# Assuming 'friends' is a list of dictionaries with 'location' keys
friend_locations = [friend['location'] for friend in friends]

# Initialize travel_time_between_friends as a 7x7 matrix
travel_time_between_friends = [[0 for _ in range(7)] for _ in range(7)]

# Calculate travel times between friends
for i in range(7):
    for j in range(7):
        from_loc = friend_locations[i]
        to_loc = friend_locations[j]
        if from_loc == to_loc:
            travel_time_between_friends[i][j] = 0
        else:
            travel_time_between_friends[i][j] = travel_time_dict[(from_loc, to_loc)]