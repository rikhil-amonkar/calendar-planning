import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00 AM
blocked = [
    # John's blocked intervals: 12:30 to 13:00 (750,780), 16:30 to 17:00 (1020,1050)
    [(750, 780), (1020, 1050)],
    # Ethan's blocked intervals: 9:00 to 10:00 (0,60), 11:30 to 12:30 (150,300), 14:00 to 14:30 (840,870)
    [(0, 60), (150, 300), (840, 870)],
    # Nicole has no blocked intervals
    []
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
    print(f"{start_hr:02d}:{start_min:02d}