for i in range(len(is_used)):
    if model.eval(is_used[i]).as_bool():  # ✅ Fixed line
        idx = model.eval(friend_idx[i]).as_long()
        friend = friends[idx]['name']
        loc_idx = model.eval(location_idx[i]).as_long()
        location_name = locations_list[loc_idx]
        start_time = model.eval(start[i]).as_long()
        end_time = model.eval(end[i]).as_long()
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        itinerary.append({
            "action": "meet",
            "location": location_name,
            "person": friend,
            "start_time": to_time_str(start_time),
            "end_time": to_time_str(end_time)
        })