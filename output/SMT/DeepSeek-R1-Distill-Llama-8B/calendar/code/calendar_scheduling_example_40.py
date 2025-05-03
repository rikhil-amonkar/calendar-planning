import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Jacob's blocked intervals: 10:00-11:00 (600,660), 11:30-12:00 (150,180), 16:00-16:30 (1440,1470)
    [(600, 660), (150, 180), (1440, 1470)],
    # Gabriel's blocked intervals: 9:30-11:30 (30,210), 13:00-13:30 (690,720), 15:00-15:30 (750,780), 16:30-17:00 (1020,1050), 17:30-18:00 (1050,1080)
    [(30, 210), (690, 720), (750, 780), (1020, 1050), (1050, 1080)],
    # Matthew's blocked intervals: 9:00-9:30 (0,30), 10:30-11:00 (90,120), 11:30-12:00 (150,180), 12:30-14:00 (210,300), 13:30-14:00 (990,1020), 15:30-16:00 (750,780), 16:30-17:00 (1020,1050), 17:30-18:00 (1050,1080)
    [(0, 30), (90, 120), (150, 180), (210, 300), (990, 1020), (750, 780), (1020, 1050), (1050, 1080)]
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