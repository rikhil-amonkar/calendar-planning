import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Jack's blocked intervals: 10:30-11:30 (90,210), 13:00-13:30 (750,780), 14:00-14:30 (900,930), 16:00-16:30 (1440,1470)
    [(90, 210), (750, 780), (900, 930), (1440, 1470)],
    # Judith's blocked intervals: 9:00-10:00 (0,60), 10:30-11:00 (90,120), 11:30-14:00 (150,420), 14:30-15:00 (750,960), 15:30-17:00 (930,1050)
    [(0, 60), (90, 120), (150, 420), (750, 960), (930, 1050)],
    # Jeffrey has no blocked intervals
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