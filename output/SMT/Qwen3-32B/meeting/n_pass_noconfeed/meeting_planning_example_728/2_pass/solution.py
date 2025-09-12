for from_loc in locations:
    for to_loc in locations:
        if from_loc == to_loc:
            travel_time_matrix[loc_to_idx[from_loc]][loc_to_idx[to_loc]] = 0
        else:
            travel_time_matrix[loc_to_idx[from_loc]][loc_to_idx[to_loc]] = travel_time_dict[from_loc][to_loc]