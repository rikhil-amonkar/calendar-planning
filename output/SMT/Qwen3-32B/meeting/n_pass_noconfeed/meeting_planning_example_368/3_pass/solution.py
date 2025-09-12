from z3 import Int, Solver, If

people_travel_time = [
    [1, 2, 3, 4],
    [5, 6, 7, 8],
    [9, 10, 11, 12],
    [13, 14, 15, 16]
]

# Example symbolic variables
prev_p = Int('prev_p')
curr_p = Int('curr_p')

# Get the expression
travel_time_expr = get_travel_time_expr(prev_p, curr_p)

# Example: Add constraints and solve
s = Solver()
s.add(prev_p == 2, curr_p == 3)
s.check()
print(s.model()[travel_time_expr])