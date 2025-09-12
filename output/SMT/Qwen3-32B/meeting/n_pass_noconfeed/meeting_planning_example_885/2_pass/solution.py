for i in range(9):
    row = []
    for j in range(9):
        loc_i = friend_locations[i]
        loc_j = friend_locations[j]
        if loc_i == loc_j:
            row.append(0)
        else:
            row.append(travel_times[(loc_i, loc_j)])
    travel_time_between_friends.append(row)