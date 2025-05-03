import z3

# Define the blocked intervals for each person as lists of tuples (a, b) in minutes since 9:00
blocked = [
    # Michelle's blocked intervals: 11:00-12:00 (660-720)
    [(660, 720)],
    # Steven's blocked intervals:
    # 9:00-9:30 (0, 30), 11:30-12:00 (690, 720), 13:30-14:00 (810, 840), 15:30-16:00 (930, 960)
    [(0, 30), (690, 720), (810, 840), (930, 960)],
    # Jerry's blocked intervals:
    # 9:00-9:30 (0,30), 10:00-11:00 (60, 660), 11:30-12:30 (690, 720), 13:00-14:30 (780, 870), 15:30-16:00 (930, 960)
    [(0, 30), (60, 660), (690, 720), (780, 870), (930, 960)]
]

# Create a Z3 context
ctx = z3.Context()

# Declare the variable for the start time
s = z3.Variable('s')

# Add constraints for each blocked interval
for person in range(3):
    for (a, b) in blocked[person]:
        # The constraint is (s + 60 <= a) OR (s >= b)
        # In Z3, this is represented as:
        # (s + 60 <= a) or (s >= b)
        # We can create these expressions using Z3's operators
        left = s + 60 <= a
        right = s >= b
        constraint = left.or(right)
        ctx.add_constraint(constraint)

# Now, solve the problem
# We need to find a value of s that satisfies all constraints.
# The possible values of s are integers between 0 and 900 (since 900 is 15:00)
# So we can loop through possible s values and check if they satisfy all constraints.
# But since Z3 can solve this, we can use it to find the solution.

# Get the solution
solution = ctx.solve()

# If solution exists, print the start time in hours:minutes format
if solution:
    s_val = solution[s].value()
    start_hr = s_val // 60
    start_min = s_val % 60
    print(f"{start_hr:02d}:{start_min:02d}")
else:
    print("No solution found")