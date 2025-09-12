for i in range(9):
    for j in range(9):
        from_loc = friends_locations[i]
        to_loc = friends_locations[j]
        if from_loc == to_loc:
            friend_travel_times[i][j] = 0
        else:
            friend_travel_times[i][j] = travel_times[(from_loc, to_loc)]