for i in range(MAX_MEETINGS):
    p = model.eval(persons[i]).as_long()
    if p != -1:
        friend = friends[p]
        s = model.eval(starts[i]).as_long()
        e = model.eval(ends[i]).as_long()
        start_time_str = minutes_to_time(s)
        end_time_str = minutes_to_time(e)
        itinerary.append({
            "action": "meet",
            "location": location_to_name[friend['location']],
            "person": friend['name'],
            "start_time": start_time_str,
            "end_time": end_time_str
        })