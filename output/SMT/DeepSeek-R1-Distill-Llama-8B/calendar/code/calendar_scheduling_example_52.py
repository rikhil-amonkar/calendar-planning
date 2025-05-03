import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Grace's blocked intervals: 9:00-9:30 (0,30), 10:00-11:00 (60,120), 16:00-16:30 (1440,1470)
    [(0, 30), (60, 120), (1440, 1470)],
    # Randy's blocked intervals: 12:30-13:00 (750,780), 16:00-16:30 (1440,1470)
    [(750, 780), (1440, 1470)],
    # Susan's blocked intervals: 9:00-14:30 (0,780), 15:30-16:00 (930,960), 16:30-17:00 (1020,1050)
    [(0, 780), (930, 960), (1020, 1050)]
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