import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Raymond's blocked intervals: 9:00-9:30 (0,30), 11:30-12:00 (690,720), 13:00-13:30 (780,810), 15:00-15:30 (900,930)
    [(0, 30), (690, 720), (780, 810), (900, 930)],
    # Billy's blocked intervals: 10:00-10:30 (60,90), 12:00-13:00 (660, 750), 16:30-17:00 (960, 1050)
    [(60, 90), (660, 750), (960, 1050)],
    # Donald's blocked intervals: 9:00-9:30 (0,30), 10:00-11:00 (60, 660), 12:00-13:00 (660, 750), 14:00-14:30 (840, 870), 16:00-17:00 (960, 1050)
    [(0, 30), (60, 660), (660, 750), (840, 870), (960, 1050)]
]

# Billy's preference to avoid meetings after 15:00 (900 minutes)
preference = s + 30 <= 900

# Create a Z3 context
ctx = z3.Context()

# Declare the variable for the start time
s = z3.Variable('s')

# Add constraints for each blocked interval
for person in range(3):
    for (a, b) in blocked[person]:
        # The constraint is (s + 30 <= a) OR (s >= b)
        left = s + 30 <= a
        right = s >= b
        constraint = left.or(right)
        ctx.add_constraint(constraint)

# Add Billy's preference constraint
ctx.add_constraint(preference)

# Now, solve the problem
solution = ctx.solve()

# If solution exists, print the start time in hours:minutes format
if solution:
    s_val = solution[s].value()
    start_hr = s_val // 60
    start_min = s_val % 60
    print(f"{start_hr:02d}:{start_min:02d}")
else:
    print("No solution found")