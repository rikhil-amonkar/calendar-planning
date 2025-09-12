# Define a Z3 function for travel time
travel_time_func = Function('travel_time', IntSort(), IntSort(), IntSort())
for i in range(11):
    for j in range(11):
        solver.add(travel_time_func(i, j) == travel_time_matrix[i][j])

# Define variables for steps
max_steps = 10
friend = [Int(f'friend_{i}') for i in range(max_steps)]
start_time = [Int(f'start_time_{i}') for i in range(max_steps)]
arrival_time = [Int(f'arrival_time_{i}') for i in range(max_steps)]

# Ensure friend[i] is in the valid range
for i in range(max_steps):
    solver.add(Or(friend[i] == -1, And(0 <= friend[i], friend[i] <= 9)))

# Initial time is 9:00 AM = 540 minutes
initial_time = 540

# Constraints for each step
for i in range(max_steps):
    if i > 0:
        for j in range(i):
            solver.add(Implies(friend[i] != -1, friend[j] != -1))

    # Duration, available_start, and available_end for this step
    duration_expr = 0
    for f in range(10):
        duration_expr = If(friend[i] == f, friends[f]['duration'], duration_expr)
    duration_expr = If(friend[i] == -1, 0, duration_expr)

    available_start_expr = 0
    for f in range(10):
        available_start_expr = If(friend[i] == f, friends[f]['available_start'], available_start_expr)
    available_start_expr = If(friend[i] == -1, 0, available_start_expr)

    available_end_expr = 0
    for f in range(10):
        available_end_expr = If(friend[i] == f, friends[f]['available_end'], available_end_expr)
    available_end_expr = If(friend[i] == -1, 0, available_end_expr)

    solver.add(Implies(friend[i] != -1, start_time[i] >= arrival_time[i]))
    solver.add(Implies(friend[i] != -1, start_time[i] >= available_start_expr))
    solver.add(Implies(friend[i] != -1, start_time[i] + duration_expr <= available_end_expr))

    # Define arrival_time[i]
    if i == 0:
        current_loc_expr = -1
        for f in range(10):
            current_loc_expr = If(friend[i] == f, friends[f]['location'], current_loc_expr)
        current_loc_expr = If(friend[i] == -1, -1, current_loc_expr)
        solver.add(Implies(friend[i] != -1, arrival_time[i] == initial_time + travel_time_func(0, current_loc_expr)))
    else:
        prev_loc_expr = -1
        for f in range(10):
            prev_loc_expr = If(friend[i - 1] == f, friends[f]['location'], prev_loc_expr)
        prev_loc_expr = If(friend[i - 1] == -1, -1, prev_loc_expr)

        current_loc_expr = -1
        for f in range(10):
            current_loc_expr = If(friend[i] == f, friends[f]['location'], current_loc_expr)
        current_loc_expr = If(friend[i] == -1, -1, current_loc_expr)

        duration_prev_expr = 0
        for f in range(10):
            duration_prev_expr = If(friend[i - 1] == f, friends[f]['duration'], duration_prev_expr)
        duration_prev_expr = If(friend[i - 1] == -1, 0, duration_prev_expr)

        solver.add(Implies(
            friend[i] != -1,
            arrival_time[i] == start_time[i - 1] + duration_prev_expr + travel_time_func(prev_loc_expr, current_loc_expr)
        ))