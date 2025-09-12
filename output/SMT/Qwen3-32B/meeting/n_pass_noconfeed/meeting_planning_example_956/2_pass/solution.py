# Compute travel time from Castro (0) to location[i]
travel_time_0_expr = travel_time[0][0]
for loc in range(1, 11):
    travel_time_0_expr = If(location[i] == loc, travel_time[0][loc], travel_time_0_expr)

solver.add(Implies(is_used[i], start_time[i] >= 540 + travel_time_0_expr))