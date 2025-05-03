import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Kevin's blocked intervals: 9:00-10:00 (0,60), 10:30-11:30 (90,210), 12:00-15:30 (360,1050), 16:30-17:00 (1020,1050)
    [(0, 60), (90, 210), (360, 1050), (1020, 1050)]
]

# Create a Z3 context
ctx = z3.Context()

# Declare the variable for the start time
s = z3.Variable('s')

# Add constraints for each blocked interval
for interval in blocked:
    a, b = interval
    # The constraint is (s + 60 <= a) OR (s >= b)
    # In Z3, this is represented as:
    # (s + 60 <= a) or (s >= b)
    left = s + 60 <= a
    right = s >= b
    constraint = left.or(right)
    ctx.add_constraint(constraint)

# Solve the problem
solution = ctx.solve()

# If solution exists, print the start time in hours:minutes format
if solution:
    s_val = solution[s].value()
    start_hr = s_val // 60
    start_min = s_val % 60
    print(f"{start_hr:02d}:{start_min:02d}")
else:
    print("No solution found")