for i in range(9):
    if model.evaluate(met[i]):
        start_time = model.evaluate(start[i]).as_long()
        end_time = model.evaluate(end[i]).as_long()
        # Convert to H:MM format
        start_h = start_time // 60
        start_m = start_time % 60
        end_h = end_time // 60
        end_m = end_time % 60
        start_str = f"{start_h}:{start_m:02d}"
        end_str = f"{end_h}:{end_m:02d}"
        person = friends[i]
        location = all_locations[friends_loc[i]]
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start_str,
            "end_time": end_str
        })