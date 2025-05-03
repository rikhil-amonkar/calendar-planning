import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Jeremy's blocked intervals: 12:00-13:00 (360,420), 13:30-14:00 (750,780), 15:00-15:30 (1080,1110)
    [(360, 420), (750, 780), (1080, 1110)],
    # Donna's blocked intervals: 9:30-10:00 (30,60), 13:00-13:30 (720,750), 16:00-17:00 (1440,1470)
    [(30, 60), (720, 750), (1440, 1470)],
    # Robert's blocked intervals: 9:00-11:00 (0,120), 11:30-12:00 (150,180), 12:30-17:00 (210,1500)
    [(0, 120), (150, 180), (210, 1500)]
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