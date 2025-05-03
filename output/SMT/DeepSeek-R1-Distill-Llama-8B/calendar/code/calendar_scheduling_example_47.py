import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Eric's blocked intervals: 9:00-9:30 (0,30), 10:30-11:30 (90,210), 15:00-15:30 (750,780)
    [(0, 30), (90, 210), (750, 780)],
    # Roger's blocked intervals: 9:30-10:30 (30,90), 11:00-12:00 (120,150), 12:30-13:00 (210,240), 14:30-15:00 (870,900), 15:30-16:30 (1020,1050)
    [(30, 90), (120, 150), (210, 240), (870, 900), (1020, 1050)],
    # David has no blocked intervals
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