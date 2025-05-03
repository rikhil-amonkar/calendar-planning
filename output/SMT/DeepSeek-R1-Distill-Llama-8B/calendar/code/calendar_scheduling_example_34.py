import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Richard's blocked intervals: 10:00-10:30 (600,630), 11:00-12:00 (120,150), 13:00-14:00 (720,780), 16:00-16:30 (1440,1470)
    [(600, 630), (120, 150), (720, 780), (1440, 1470)],
    # Noah's blocked intervals: 10:00-10:30 (600,630), 11:30-13:00 (240,300), 13:30-14:00 (750,780), 16:00-17:00 (1440,1500)
    [(600, 630), (240, 300), (750, 780), (1440, 1500)]
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