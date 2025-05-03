import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Brandon's blocked intervals: 11:30-12:00 (150,180), 12:30-13:00 (750,780), 14:00-14:30 (600,630)
    [(150, 180), (750, 780), (600, 630)],
    # Donna's blocked intervals: 10:00-10:30 (60,90), 12:00-12:30 (360,390)
    [(60, 90), (360, 390)],
    # Jack's blocked intervals: 9:30-10:00 (30,60), 10:30-11:00 (90,120), 11:30-12:30 (150,210), 13:00-14:30 (240,300), 14:30-15:00 (870,900), 16:00-16:30 (1440,1470), 17:00-17:30 (1500,1530)
    [(30, 60), (90, 120), (150, 210), (240, 300), (870, 900), (1440, 1470), (1500, 1530)]
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