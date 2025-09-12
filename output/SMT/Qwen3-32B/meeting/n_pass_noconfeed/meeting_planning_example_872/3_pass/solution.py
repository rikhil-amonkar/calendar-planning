num_positions = len(friend_vars)

itinerary = []
for i in range(num_positions):
    f_idx_val = model.evaluate(friend_vars[i]).as_long()
    if f_idx_val != 9:
        start = model.evaluate(start_vars[i]).as_long()
        end = model.evaluate(end_vars[i]).as_long()
        friend = friends[f_idx_val]
        # Convert start and end to H:MM format
        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": to_time(start),
            "end_time": to_time(end)
        })