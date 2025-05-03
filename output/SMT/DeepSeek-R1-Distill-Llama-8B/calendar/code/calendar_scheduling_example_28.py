import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Brittany's blocked intervals: 13:00-13:30 (720,750), 16:00-16:30 (1440,1470)
    [(720, 750), (1440, 1470)],
    # Doris's blocked intervals: 9:00-11:00 (0,210), 11:30-14:30 (240,870), 15:00-17:00 (1080,1050)
    [(0, 210), (240, 870), (1080, 1050)]
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