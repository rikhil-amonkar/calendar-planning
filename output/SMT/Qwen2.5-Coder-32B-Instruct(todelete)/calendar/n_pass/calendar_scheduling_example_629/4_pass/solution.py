from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0  # 9:00
work_end = 480  # 17:00

# Margaret's blocked times on Monday
margaret_blocked_times_monday = [
    (210, 240),  # 10:30 to 11:00
    (270, 300),  # 11:30 to 12:00
    (360, 390),  # 13:00 to 13:30
    (540, 720)   # 15:00 to 17:00
]

# Alexis's blocked times on Monday
alexis_blocked_times_monday = [
    (90, 300),  # 9:30 to 11:30
    (390, 420), # 12:30 to 13:00
    (480, 720)  # 14:00 to 17:00
]

# Margaret's blocked times on Tuesday
margaret_blocked_times_tuesday = [
    (720, 750)  # 12:00 to 12:30
]

# Alexis's blocked times on Tuesday
alexis_blocked_times_tuesday = [
    (0, 540),   # 9:00 to 15:00
    (870, 1020) # 14:30 to 17:00
]

# Margaret's additional constraints
margaret_additional_constraints = [
    (0, 0, 0),  # No meetings on Monday
    (1, 870, 1020) # Meetings on Tuesday after 14:30 (870 minutes from 9:00)
]

# Add constraints for work hours
constraints.append(And(start_time >= work_start, start_time + meeting_duration <= work_end))

# Add constraints for Margaret's blocked times on Monday
for blocked_start, blocked_end in margaret_blocked_times_monday:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add constraints for Alexis's blocked times on Monday
for blocked_start, blocked_end in alexis_blocked_times_monday:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add constraints for Margaret's blocked times on Tuesday
for blocked_start, blocked_end in margaret_blocked_times_tuesday:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add constraints for Alexis's blocked times on Tuesday
for blocked_start, blocked_end in alexis_blocked_times_tuesday:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add constraints for Margaret's additional constraints
for d, blocked_start, blocked_end in margaret_additional_constraints:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end)))

# Define the solver
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = 9 + model[start_time].as_long() // 60
    meeting_start_minute = model[start_time].as_long() % 60
    meeting_end_time = meeting_start_time + meeting_duration // 60
    meeting_end_minute = meeting_start_minute + meeting_duration % 60
    if meeting_end_minute >= 60:
        meeting_end_time += 1
        meeting_end_minute -= 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_time:02}:{meeting_end_minute:02}")
else:
    print("No solution found")