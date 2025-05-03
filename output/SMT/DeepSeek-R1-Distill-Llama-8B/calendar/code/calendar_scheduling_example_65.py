import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # John's blocked intervals: 12:30-13:00 (750,780), 15:30-16:00 (990,1020)
    [(750, 780), (990, 1020)],
    # Andrea's blocked intervals: 9:00-9:30 (0,30), 11:00-12:30 (120,300), 14:00-14:30 (840,870), 15:00-15:30 (960,990), 16:00-16:30 (1080,1050)
    [(0, 30), (120, 300), (840, 870), (960, 990), (1080, 1050)],
    # Lisa's blocked intervals: 9:00-10:00 (0,60), 10:30-11:00 (90,120), 12:00-12:30 (180,210), 14:00-14:30 (840,870), 15:00-15:30 (960,990), 16:00-16:30 (1080,1050)
    [(0, 60), (90, 120), (180, 210), (840, 870), (960, 990), (1080, 1050)]
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