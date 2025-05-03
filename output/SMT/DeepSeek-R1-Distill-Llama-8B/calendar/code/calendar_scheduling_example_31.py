import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Richard's blocked intervals: 13:30-14:00 (750,780), 15:00-15:30 (1080,1110)
    [(750, 780), (1080, 1110)],
    # Martha's blocked intervals: 9:00-9:30 (0,30), 13:00-13:30 (720,750), 14:00-14:30 (840,870)
    [(0, 30), (720, 750), (840, 870)],
    # Kimberly's blocked intervals: 9:00-11:00 (0,240), 11:30-12:00 (240,300), 12:30-13:00 (360,390), 14:00-16:00 (600,960), 15:30-16:00 (990,1020), 16:00-16:30 (1080,1110), 16:30-17:00 (1110,1140)
    [(0, 240), (240, 300), (360, 390), (600, 960), (990, 1020), (1080, 1110), (1110, 1140)]
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