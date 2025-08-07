from z3 import *

# Define meetings with their durations and attendees
meetings = [
    (2, [0, 1]),  # Meeting 0: duration 2 hours, attendees 0 and 1
    (3, [0, 2]),  # Meeting 1: duration 3 hours, attendees 0 and 2
    (4, [1, 2]),  # Meeting 2: duration 4 hours, attendees 1 and 2
    (1, [0, 1, 2])  # Meeting 3: duration 1 hour, all attendees
]

# Business hours constraints (only start time enforced)
business_start = 9
n_participants = 3
n_meetings = len(meetings)

# Create start time variables for each meeting
starts = [Int(f'start_{i}') for i in range(n_meetings)]

# Create end time variables for each meeting
ends = [starts[i] + meetings[i][0] for i in range(n_meetings)]

# Makespan is the latest end time of any meeting
makespan = Int('makespan')

# Create solver instance
s = Optimize()

# Constraint: meetings must start at or after business hours
for i in range(n_meetings):
    s.add(starts[i] >= business_start)

# Constraints for non-overlapping meetings with shared attendees
for i in range(n_meetings):
    for j in range(i + 1, n_meetings):
        shared_attendees = set(meetings[i][1]).intersection(meetings[j][1])
        if shared_attendees:
            s.add(Or(starts[i] >= ends[j], starts[j] >= ends[i]))

# Makespan must be at least as large as every meeting's end time
for i in range(n_meetings):
    s.add(makespan >= ends[i])

# Set objective to minimize makespan
s.minimize(makespan)

# Solve and output results
if s.check() == sat:
    model = s.model()
    solution = []
    for i in range(n_meetings):
        start_val = model.eval(starts[i]).as_long()
        end_val = start_val + meetings[i][0]
        solution.append((start_val, end_val))
    makespan_val = model.eval(makespan).as_long()
    
    print("Meeting Schedule:")
    for i, (start, end) in enumerate(solution):
        print(f"Meeting {i}: {start}:00 to {end}:00")
    print(f"Makespan: {makespan_val}:00")
else:
    print("No valid schedule exists.")