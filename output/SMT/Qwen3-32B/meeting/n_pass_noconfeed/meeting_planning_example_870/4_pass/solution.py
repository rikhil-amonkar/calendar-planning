from ortools.sat.python import cp_model

# Initialize model and solver
model = cp_model.CpModel()
solver = cp_model.CpSolver()

# Assume the following variables are already defined in the context:
# - met: list of boolean variables indicating if a meeting is scheduled
# - start: list of integer variables for meeting start times
# - end: list of integer variables for meeting end times
# - friends: list of friend names
# - friends_loc: list of friend locations
# - all_locations: mapping from location IDs to location names
# - itinerary: list to store the final itinerary

# Assume the model has already been built and constraints added
# Solve the model
status = solver.Solve(model)

# Only process results if a solution was found
if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    for i in range(9):
        if solver.Value(met[i]):
            start_time = solver.Value(start[i])
            end_time = solver.Value(end[i])
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