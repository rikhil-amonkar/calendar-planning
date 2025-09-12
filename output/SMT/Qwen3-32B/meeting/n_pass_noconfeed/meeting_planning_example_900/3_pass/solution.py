# Add bounds to ensure friend variables are valid
for i in range(num_steps):
    solver.add(z3.And(friends_vars[i] >= -1, friends_vars[i] <= len(friends) - 1))

# ... [rest of the constraints and optimization setup]

# Solve and output the result
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(num_steps):
        friend_val = model.eval(friends_vars[i]).as_long()
        if friend_val != -1:
            friend_idx = friend_val
            location = model.eval(location_vars[i]).as_long()
            start_time = model.eval(start_time_vars[i]).as_long()
            end_time = model.eval(end_time_vars[i]).as_long()
            name = friends[friend_idx]['name']
            def to_time_str(t):
                hours = t // 60
                minutes = t % 60
                return f"{hours}:{minutes:02d}"
            itinerary.append({
                "action": "meet",
                "location": location_names[location],
                "person": name,
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")