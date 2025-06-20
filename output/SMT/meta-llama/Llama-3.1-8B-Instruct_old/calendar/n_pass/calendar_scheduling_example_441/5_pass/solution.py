from z3 import *

# Define the time slots
slots = []
for h in range(9, 17):
    for m in range(0, 60, 30):
        slots.append((h, m))

# Define the participants and their constraints
participants = {
    'Joan': [(11, 30), (14, 30)],
    'Megan': [(9, 0), (14, 0), (16, 0)],
    'Austin': [],
    'Betty': [(9, 30), (11, 30), (13, 30), (16, 0)],
    'Judith': [(9, 0), (12, 0), (14, 0)],
    'Terry': [(9, 30), (11, 30), (13, 0), (15, 0), (16, 0)],
    'Kathryn': [(9, 30), (10, 30), (11, 30), (14, 0), (16, 0), (16, 30)]
}

# Define the variables
day = 'Monday'
meeting_duration = 30
start_time, end_time = 9, 17
solver = Solver()

# Define the variables for the meeting time
meeting_start, meeting_end = Int('meeting_start'), Int('meeting_end')
meeting_start_var = [Bool(f'meeting_start_{i}') for i in range(len(slots))]
meeting_end_var = [Bool(f'meeting_end_{i}') for i in range(len(slots))]
meeting_duration_var = [Bool(f'meeting_duration_{i}') for i in range(len(slots))]
meeting_time_var = [Int(f'meeting_time_{i}') for i in range(len(slots))]

# Define the constraints
for i, (h, m) in enumerate(slots):
    meeting_start_var[i] = meeting_start >= h * 60 + m
    meeting_end_var[i] = meeting_end <= (h + 1) * 60 + m
    meeting_time_var[i] = If(meeting_start_var[i], meeting_start, (h + 1) * 60 + m)

    # Ensure the meeting duration is 30 minutes
    meeting_duration_var[i] = meeting_time_var[i] + meeting_duration <= meeting_end_var[i]

    # Ensure the meeting does not conflict with any participant's schedule
    for participant, constraints in participants.items():
        for constraint in constraints:
            conflict_start, conflict_end = constraint
            conflict_start_var = conflict_start * 60
            conflict_end_var = conflict_end * 60
            conflict = And(conflict_start_var <= meeting_time_var[i], meeting_time_var[i] + meeting_duration <= conflict_end_var)
            solver.add(Not(conflict))

# Solve the constraints
solver.add(meeting_start >= 9 * 60)
solver.add(meeting_end <= 17 * 60)
solver.add(Or([meeting_start_var[i] for i in range(len(slots))]))

if solver.check() == sat:
    model = solver.model()
    meeting_start_value = None
    for i in range(len(slots)):
        if model[meeting_start_var[i]]:
            meeting_start_value = model[meeting_time_var[i]].as_long()
            break
    start_time = meeting_start_value // 60
    end_time = (meeting_start_value // 60 + meeting_duration) % 24
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time:02d}:00\nEnd Time: {end_time:02d}:00")
else:
    print("No solution found.")