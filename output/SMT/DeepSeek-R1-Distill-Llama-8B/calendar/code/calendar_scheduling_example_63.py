import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Judith's blocked intervals: 10:00-10:30 (90,120), 11:00-12:00 (150,180), 12:30-13:00 (210,240)
    [(90, 120), (150, 180), (210, 240)],
    # Roger's blocked intervals: 9:00-9:30 (0,30), 10:30-11:00 (90,120), 12:00-12:30 (180,210), 13:00-13:30 (240,270), 14:00-14:30 (300,330), 16:00-17:00 (360,390)
    [(0, 30), (90, 120), (180, 210), (240, 270), (300, 330), (360, 390)],
    # Madison has no blocked intervals
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
    print(f"{start_hr:02d}:{start_min:02d}")
else:
    print("No solution found")