import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Nancy's blocked intervals: 11:00-12:30 (120,210), 13:00-13:30 (720,750), 14:00-15:00 (840,870)
    [(120, 210), (720, 750), (840, 870)],
    # Patricia's blocked intervals: 10:00-12:00 (60,210), 12:30-13:00 (390,420), 13:30-16:00 (780,960), 14:00-14:30 (840,870), 15:00-15:30 (900,930), 16:30-17:00 (1020,1050)
    [(60, 210), (390, 420), (780, 960), (840, 870), (900, 930), (1020, 1050)]
]

# Create a Z3 context
ctx = z3.Context()

# Declare the variable for the start time
s = z3.Variable('s')

# Add constraints for each blocked interval
for person in range(2):
    for (a, b) in blocked[person]:
        # The constraint is (s + 60 <= a) OR (s >= b)
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