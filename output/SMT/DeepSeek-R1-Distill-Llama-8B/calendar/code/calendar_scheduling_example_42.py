import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Julie's blocked intervals: 9:00-9:30 (0,30), 11:00-11:30 (120,150), 12:00-12:30 (180,210), 13:30-14:00 (750,780), 16:00-17:00 (1440,1470)
    [(0, 30), (120, 150), (180, 210), (750, 780), (1440, 1470)],
    # Sean's blocked intervals: 9:00-9:30 (0,30), 13:00-13:30 (720,750), 15:00-15:30 (1080,1110), 16:00-16:30 (1440,1470)
    [(0, 30), (720, 750), (1080, 1110), (1440, 1470)],
    # Lori's blocked intervals: 10:00-10:30 (60,90), 11:00-13:00 (120,300), 15:30-17:00 (930,1050), 16:30-17:00 (1020,1050)
    [(60, 90), (120, 300), (930, 1050), (1020, 1050)]
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