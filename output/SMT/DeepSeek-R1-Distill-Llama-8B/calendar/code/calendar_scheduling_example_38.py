import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Catherine's blocked intervals: 10:30-11:00 (150,180), 12:30-13:00 (750,780), 14:30-15:00 (870,900)
    [(150, 180), (750, 780), (870, 900)],
    # Michael's blocked intervals: 9:30-10:30 (30,90), 12:00-13:00 (360,420), 13:30-14:00 (750,780), 15:00-15:30 (1080,1110)
    [(30, 90), (360, 420), (750, 780), (1080, 1110)],
    # Alexander's blocked intervals: 9:00-9:30 (0,30), 10:00-10:30 (60,90), 11:00-12:00 (120,150), 13:00-13:30 (240,270), 14:00-14:30 (300,330), 15:00-15:30 (1080,1110), 16:00-16:30 (1440,1470), 17:00-17:30 (1500,1530)
    [(0, 30), (60, 90), (120, 150), (240, 270), (300, 330), (1080, 1110), (1440, 1470), (1500, 1530)]
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