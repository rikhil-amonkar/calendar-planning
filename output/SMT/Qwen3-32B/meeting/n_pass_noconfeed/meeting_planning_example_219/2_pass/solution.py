for i, friend in enumerate(perm):
    friend_info = friends_data[friend]
    current_loc = friend_info['location']
    s = model.evaluate(Int(f's_{friend}_{i}')).as_long()  # Fixed line
    end_time = s + friend_info['min_duration']
    start_hm = f"{(s // 60)}:{(s % 60):02d}"
    end_hm = f"{(end_time // 60)}:{(end_time % 60):02d}"
    itinerary.append({
        "action": "meet",
        "location": current_loc,
        "person": friend,
        "start_time": start_hm,
        "end_time": end_hm
    })
    prev_time = end_time
    prev_loc = current_loc