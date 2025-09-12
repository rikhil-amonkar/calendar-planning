for i in range(len(friends)):
    row = []
    for j in range(len(friends)):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        if loc_i == loc_j:
            row.append(0)
        else:
            row.append(travel_times[(loc_i, loc_j)])
    travel_time_matrix.append(row)