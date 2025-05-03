import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Lisa's blocked intervals: 9:00-10:00 (0,60), 10:30-11:30 (90,210), 12:30-13:00 (750,780), 16:00-16:30 (1440,1470)
    [(0, 60), (90, 210), (750, 780), (1440, 1470)],
    # Bobby's blocked intervals: 9:00-9:30 (0,30), 10:00-10:30 (60,90), 11:30-12:00 (240,300), 15:00-15:30 (1080,1110)
    [(0, 30), (60, 90), (240, 300), (1080, 1110)],
    # Randy's blocked intervals: 9:30-10:00 (30,60), 10:30-11:00 (90,120), 11:30-12:30 (240,300), 13:00-13:30 (780,810), 14:30-15:30 (870,1050), 16:00-16:30 (1440,1470), 17:00-17:30 (1530,1560)
    [(30, 60), (90, 120), (240, 300), (780, 810), (870, 1050), (1440, 1470), (1530, 1560)]
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