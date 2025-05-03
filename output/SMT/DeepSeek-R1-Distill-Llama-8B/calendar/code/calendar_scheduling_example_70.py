import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Denise's blocked intervals: 12:00-12:30 (360, 390), 15:30-16:00 (930, 960)
    [(360, 390), (930, 960)],
    # Angela has no blocked intervals
    [],
    # Natalie's blocked intervals: 9:00-11:30 (0,210), 12:00-12:30 (360, 390), 13:00-13:30 (780, 810), 14:00-14:30 (840, 870), 16:00-16:30 (960, 1050)
    [(0, 210), (360, 390), (780, 810), (840, 870), (960, 1050)]
]

# Create a Z3 context
ctx = z3.Context()

# Declare the variable for the start time
s = z3.Variable('s')

# Add constraints for each blocked interval
for person in range(3):
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