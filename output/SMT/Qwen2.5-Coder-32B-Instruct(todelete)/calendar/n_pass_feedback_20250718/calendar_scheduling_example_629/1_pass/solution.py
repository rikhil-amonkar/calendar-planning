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

# Margaret's blocked times
margaret_blocked_times = [
    (210, 240),  # 10:30 to 11:00
    (270, 300),  # 11:30 to 12:00
    (360, 390),  # 13:00 to 13:30
    (540, 720)   # 15:00 to 17:00
]

# Alexis's blocked times
alexis_blocked_times = [
    (90, 300),  # 9:30 to 11:30
    (390, 420), # 12:30 to 13:00
    (480, 720)  # 14:00 to 17:00
]

# Additional constraints for Tuesday
tuesday_additional_constraints = [
    (0, 870)  # 9:00 to 14:30
]

# Margaret does not want to meet on Monday
constraints.append(day == 1)

# Meeting must be within work hours
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Meeting must not overlap with Margaret's blocked times
for blocked_start, blocked_end in margaret_blocked_times:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Meeting must not overlap with Alexis's blocked times
for blocked_start, blocked_end in alexis_blocked_times:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Additional constraints for Tuesday
for blocked_start, blocked_end in tuesday_additional_constraints:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Create the solver and add the constraints
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
        meeting_end_minute -= 60
        meeting_end_time += 1

    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_time:02}:{meeting_end_minute:02}")
else:
    print("No solution found")