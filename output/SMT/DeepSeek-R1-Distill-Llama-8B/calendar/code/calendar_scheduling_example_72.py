import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Amy's blocked intervals: 9:30-10:30 (30,90), 12:00-12:30 (360,390), 13:00-13:30 (750,780)
    [(30, 90), (360, 390), (750, 780)],
    # Christopher's blocked intervals: 9:00-10:30 (0,90), 11:00-11:30 (150,150), 12:00-12:30 (360,390), 13:00-13:30 (900,930)
    [(0,90), (150,150), (360,390), (750,780), (900,930)
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
    print(f"{start_hr:02d}:{start_min:02d}