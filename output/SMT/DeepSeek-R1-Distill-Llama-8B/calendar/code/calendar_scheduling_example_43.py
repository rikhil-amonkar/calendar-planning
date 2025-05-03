import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Albert's blocked intervals: 9:30-10:30 (30,90), 12:00-12:30 (360,390), 14:00-14:30 (600,630), 15:00-15:30 (750,780), 16:30-17:00 (1020,1050)
    [(30, 90), (360, 390), (600, 630), (750, 780), (1020, 1050)],
    # Gregory's blocked intervals: 11:00-11:30 (120,150), 12:30-13:00 (360,420), 13:30-14:00 (750,780), 15:30-16:00 (990,1020)
    [(120, 150), (360, 420), (750, 780), (990, 1020)],
    # Benjamin's blocked intervals: 9:30-10:00 (30,60), 10:30-11:00 (90,120), 11:30-13:30 (150,300), 14:00-15:00 (600,780), 15:30-16:00 (750,960), 16:30-17:00 (1020,1050)
    [(30, 60), (90, 120), (150, 300), (600, 780), (750, 960), (1020, 1050)]
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