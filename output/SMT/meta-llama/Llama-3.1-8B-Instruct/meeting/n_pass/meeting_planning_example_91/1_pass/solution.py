from z3 import *

# Define the variables
start_time = Int('start_time')
end_time = Int('end_time')
travel_time_russian_hill_to_richmond_district = 14
travel_time_richmond_district_to_russian_hill = 13
min_meeting_duration = 75

# Define the constraints
solver = Optimize()

# Daniel is available from 7:00PM to 8:15PM
daniel_available_start = 19 * 60  # 7:00PM in minutes
daniel_available_end = 19 * 60 + 15 * 60  # 8:15PM in minutes

# You arrive at Russian Hill at 9:00AM
arrival_time = 9 * 60  # 9:00AM in minutes

# You must meet Daniel for at least 75 minutes
meeting_duration = (end_time - start_time) >= min_meeting_duration

# You must travel to Richmond District and back
travel_time = If(start_time < daniel_available_start,
                 travel_time_russian_hill_to_richmond_district + travel_time_richmond_district_to_russian_hill,
                 travel_time_russian_hill_to_richmond_district)

# Daniel is not available before 7:00PM
daniel_unavailable_before = start_time >= daniel_available_start

# Daniel is available after 7:00PM
daniel_available_after = end_time <= daniel_available_end

# Meeting duration must be at least 75 minutes
meeting_duration = (end_time - start_time) >= min_meeting_duration

# Add the constraints to the solver
solver.add([meeting_duration, daniel_unavailable_before, daniel_available_after, travel_time])

# Minimize the total time spent
solver.minimize(end_time - arrival_time)

# Solve the optimization problem
solution = solver.check()

if solution == sat:
    model = solver.model()
    start_time_value = model[start_time].as_long()
    end_time_value = model[end_time].as_long()
    print(f"Best schedule: Meet Daniel from {start_time_value // 60}:{start_time_value % 60} to {end_time_value // 60}:{end_time_value % 60}")
else:
    print("No solution found")