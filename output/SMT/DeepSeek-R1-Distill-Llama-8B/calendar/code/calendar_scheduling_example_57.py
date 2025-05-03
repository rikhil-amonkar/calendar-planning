import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Virginia's blocked intervals: 10:00-12:00 (600,720)
    [(600, 720)],
    # Charles's blocked intervals: 12:00-12:30 (360,390), 13:00-13:30 (750,780), 14:00-14:30 (840,870)
    [(360, 390), (750, 780), (840, 870)],
    # Megan's blocked intervals: 9:00-12:00 (0,360), 14:00-14:30 (600,630), 16:00-16:30 (1440,1470), 17:00-17:30 (1500,1530)
    [(0, 360), (600, 630), (1440, 1470), (1500, 1530)]
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