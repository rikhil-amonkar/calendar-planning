import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Emily's blocked intervals: 10:00-10:30 (600,630), 11:30-12:30 (150,210), 14:00-15:00 (840,1050), 16:00-16:30 (1440,1470)
    [(600, 630), (150, 210), (840, 1050), (1440, 1470)],
    # Melissa's blocked intervals: 9:30-10:00 (30,60), 14:30-15:00 (870,900)
    [(30, 60), (870, 900)],
    # Frank's blocked intervals: 10:00-10:30 (600,630), 11:00-11:30 (120,150), 12:30-13:00 (390,420), 13:30-14:30 (990,1020), 14:00-15:00 (960,1050), 15:30-16:00 (1110,1170), 16:00-16:30 (1140,1170)
    [(600, 630), (120, 150), (390, 420), (990, 1020), (960, 1050), (1110, 1170), (1140, 1170)]
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