for friend in friends.values():
    location = friend['location']
    start_time = friend['start_time']
    end_time = friend['end_time']
    meeting_time = friend['meeting_time']
    
    for i in range(max(0, (start_time - meeting_time) // time_step), min(end_time // time_step, (end_time + meeting_time) // time_step)):
        if i in range(len(locations_var)) and i in range(len(times_var)):
            solver.add(And(locations_var[locations.index(location)], times_var[i]))