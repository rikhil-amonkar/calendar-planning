import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Janet's blocked intervals: 9:30-10:30 (30,90), 12:30-13:00 (750,780), 14:00-14:30 (600,630)
    [(30, 90), (750, 780), (600, 630)],
    # Cynthia's blocked intervals: 9:30-10:00 (30,60), 11:00-11:30 (120,150), 12:30-14:30 (750,780), 16:00-17:00 (960,1050)
    [(30, 60), (120, 150), (750, 780), (960, 1050)],
    # Rachel has no blocked intervals
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