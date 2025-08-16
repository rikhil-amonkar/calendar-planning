def next_location(current_time, current_loc):
    options = []
    for person, constraint in constraints.items():
        if can_meet(person, current_time):
            # Check if the current location is the same as the target location
            if current_loc == constraint['location']:
                travel_time = 0
            else:
                travel_time = travel_times[(current_loc, constraint['location'])]
            meet_start = current_time + timedelta(minutes=travel_time)
            meet_end = meet_start + timedelta(minutes=constraint['min_duration'])
            if parse_time(constraint['end']) >= meet_end:
                options.append((person, meet_start, meet_end))
    return sorted(options, key=lambda x: x[1])