for prev in range(5):
    for curr in range(5):
        prev_loc = friends[prev]['location']
        curr_loc = friends[curr]['location']
        if prev_loc == curr_loc:
            travel_times_between_friends[prev][curr] = 0
        else:
            travel_times_between_friends[prev][curr] = travel_times[(prev_loc, curr_loc)]