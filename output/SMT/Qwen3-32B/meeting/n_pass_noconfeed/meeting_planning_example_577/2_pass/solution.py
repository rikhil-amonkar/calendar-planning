for k in range(5):
    for m in range(5):
        loc_k = friends_locations[k]
        loc_m = friends_locations[m]
        if loc_k == loc_m:
            travel_time_matrix[k][m] = 0
        else:
            travel_time_matrix[k][m] = travel_time[loc_k][loc_m]