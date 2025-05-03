import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Joan's blocked intervals: 11:00-11:30 (120,150), 12:30-13:00 (750,780)
    [(120, 150), (750, 780)],
    # Theresa's blocked intervals: 12:00-12:30 (180,210), 15:00-15:30 (1080,1110)
    [(180, 210), (1080, 1110)],
    # Shirley's blocked intervals: 9:30-10:30 (30,90), 11:00-12:00 (150,180), 13:00-14:00 (360,420), 15:30-16:30 (750,960)
    [(30, 90), (150, 180), (360, 420), (750, 960)]
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