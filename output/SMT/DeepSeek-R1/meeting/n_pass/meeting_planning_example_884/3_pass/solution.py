from z3 import *

# Define the meetings with their details: (id, duration, value, available_start, available_end, recurrence)
meetings = [
    (0, 60, 10, 9*60, 12*60, 1),
    (1, 90, 20, 9*60, 12*60, 2),
    (2, 120, 30, 13*60, 17*60, 4),
]

n = len(meetings)

# Create Z3 variables for start times and inclusion flags
start = [Int(f'start_{i}') for i in range(n)]
include = [Bool(f'include_{i}') for i in range(n)]

# Create an Optimize context for maximization
opt = Optimize()

# Add constraints for each meeting
for i in range(n):
    id, duration, value, av_start, av_end, recurrence = meetings[i]
    # If included, meeting must be within available time and working hours (9:00-17:00)
    opt.add(Implies(include[i], And(start[i] >= av_start, start[i] + duration <= av_end)))
    opt.add(Implies(include[i], And(start[i] >= 9*60, start[i] + duration <= 17*60)))

# Add non-overlapping constraints for included meetings
for i in range(n):
    for j in range(i+1, n):
        dur_i = meetings[i][1]
        dur_j = meetings[j][1]
        opt.add(Implies(And(include[i], include[j]),
                       Or(start[i] + dur_i <= start[j],
                          start[j] + dur_j <= start[i])))

# Compute earliest start time iteratively
earliest_start = 24*60  # Initialize with a large value (24 hours in minutes)
for i in range(n):
    earliest_start = If(And(include[i], start[i] < earliest_start), start[i], earliest_start)

# Compute latest end time iteratively
latest_end = 0  # Initialize with 0
for i in range(n):
    end_i = start[i] + meetings[i][1]
    latest_end = If(And(include[i], end_i > latest_end), end_i, latest_end)

# Time span constraint: latest_end - earliest_start <= 480 minutes (8 hours)
# If no meetings are included, span is negative (0 - 24*60) which is <= 480
span = latest_end - earliest_start
opt.add(span <= 480)

# Total value calculation: sum of values of included meetings
total_value = Sum([If(include[i], meetings[i][2], 0) for i in range(n)])

# Maximize the total value
opt.maximize(total_value)

# Solve and output the schedule if a solution exists
if opt.check() == sat:
    m = opt.model()
    print("Optimal schedule:")
    for i in range(n):
        if m.evaluate(include[i]):
            s_val = m.evaluate(start[i])
            start_hour = s_val.as_long() // 60
            start_min = s_val.as_long() % 60
            end_val = s_val.as_long() + meetings[i][1]
            end_hour = end_val // 60
            end_min = end_val % 60
            print(f"Meeting {i}: {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
        else:
            print(f"Meeting {i}: Not scheduled")
    total_val = m.evaluate(total_value)
    print(f"Total value: {total_val}")
else:
    print("No solution found")