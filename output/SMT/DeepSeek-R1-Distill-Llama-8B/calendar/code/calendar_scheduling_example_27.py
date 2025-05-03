import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Jesse's blocked intervals: 10:00-10:30 (600,630), 15:30-16:00 (990,1020)
    [(600, 630), (990, 1020)],
    # Megan's blocked intervals: 10:30-11:00 (90,120), 11:30-12:30 (240,300), 13:30-14:30 (780,870), 15:00-16:30 (900,1050)
    [(90, 120), (240, 300), (780, 870), (900, 1050)]
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