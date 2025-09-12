from ortools.sat.python import cp_model

# Example for OR-Tools
solver = cp_model.CpSolver()
status = solver.Solve(model)

if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    itinerary = []
    for i in range(len(is_used)):
        if solver.Value(is_used[i]):
            idx = solver.Value(friend_idx[i])
            friend = friends[idx]['name']
            loc_idx = solver.Value(location_idx[i])
            location_name = locations_list[loc_idx]
            start_time = solver.Value(start[i])
            end_time = solver.Value(end[i])

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
    print(itinerary)