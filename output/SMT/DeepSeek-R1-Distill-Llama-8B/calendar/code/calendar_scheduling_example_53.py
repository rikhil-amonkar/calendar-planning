import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Alice's blocked intervals: 9:30-10:00 (30,60), 12:30-13:00 (750,780), 14:30-15:00 (600,630)
    [(30, 60), (750, 780), (600, 630)],
    # Arthur's blocked intervals: 9:00-9:30 (0,30), 10:00-11:00 (60,120), 11:30-12:00 (150,180), 13:00-13:30 (240,270), 14:30-15:00 (870,900), 16:00-16:30 (1440,1470)
    [(0, 30), (60, 120), (150, 180), (240, 270), (870, 900), (1440, 1470)],
    # Noah has no blocked intervals
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