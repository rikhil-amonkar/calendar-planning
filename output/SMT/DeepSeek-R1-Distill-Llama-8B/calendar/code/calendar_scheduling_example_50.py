import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Emma's blocked intervals: 9:00-10:30 (0,90), 11:00-12:00 (120,150), 12:30-13:30 (210,330), 14:30-15:30 (450,570), 16:00-16:30 (480,600)
    [(0, 90), (120, 150), (210, 330), (450, 570), (480, 600)],
    # Daniel and Roy have no blocked intervals
    []
]

# Create a Z3 context
ctx = z3.Context()

# Declare the variable for the start time
s = z3.Variable('s')

# Add constraints for each blocked interval
for interval in blocked:
    a, b = interval
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