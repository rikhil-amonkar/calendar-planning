import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Ronald's blocked intervals: 11:30-12:00 (150,180), 14:00-14:30 (600,630), 16:00-17:00 (1440,1470)
    [(150, 180), (600, 630), (1440, 1470)],
    # Amanda's blocked intervals: 9:30-12:00 (30,360), 12:30-13:00 (390,420), 13:30-14:00 (780,810), 15:30-17:00 (930,1050)
    [(30, 360), (390, 420), (780, 810), (930, 1050)],
    # Isabella has no blocked intervals
    []
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