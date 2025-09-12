# Define is_used as a list of boolean variables from the model
# For example:
# is_used = [model.NewBoolVar(f"is_used_{i}") for i in range(num_possible_meetings)]

# Example placeholder (for testing only)
is_used = [True, False, True]  # Replace with actual model variables

num_steps = len(is_used)

for i in range(num_steps):
    if is_true(model.eval(is_used[i])):
        friend_idx = model.eval(friends_vars[i]).as_long()
        start_time = model.eval(start_times[i]).as_long()
        min_duration = model.eval(Select(min_duration_array, friend_idx)).as_long()
        end_time = start_time + min_duration
        friend = friends[friend_idx]
        # Convert to time strings
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        start_str = to_time_str(start_time)
        end_str = to_time_str(end_time)
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_str,
            "end_time": end_str
        })