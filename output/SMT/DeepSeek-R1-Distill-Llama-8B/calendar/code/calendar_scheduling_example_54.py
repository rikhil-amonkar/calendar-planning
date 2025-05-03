import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Isabella's blocked intervals: 11:00-11:30 (120,150), 15:30-16:00 (990,1020)
    [(120, 150), (990, 1020)],
    # Tyler's blocked intervals: 9:00-10:00 (0,60), 16:00-16:30 (1440,1470)
    [(0, 60), (1440, 1470)],
    # Jordan's blocked intervals: 9:00-10:00 (0,60), 10:30-11:00 (90,120), 12:30-13:00 (750,780), 14:00-14:30 (600,630), 15:00-16:00 (750,960), 16:30-17:00 (1020,1050)
    [(0, 60), (90, 120), (750, 780), (600, 630), (750, 960), (1020, 1050)]
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