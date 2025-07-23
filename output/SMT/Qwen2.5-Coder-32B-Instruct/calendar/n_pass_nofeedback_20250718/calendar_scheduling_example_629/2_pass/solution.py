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
    (60, 90),  # 10:30 to 11:00
    (90, 120), # 11:30 to 12:00
    (180, 210),# 13:00 to 13:30
    (300, 480) # 15:00 to 17:00
]

# Alexis's blocked times on Monday
alexis_blocked_times_monday = [
    (30, 120), # 9:30 to 11:30
    (180, 210),# 12:30 to 13:00
    (240, 480) # 14:00 to 17:00
]

# Margaret's blocked times on Tuesday
margaret_blocked_times_tuesday = [
    (180, 210) # 12:00 to 12:30
]

# Alexis's blocked times on Tuesday
alexis_blocked_times_tuesday = [
    (0, 30),   # 9:00 to 9:30
    (30, 60),  # 10:00 to 10:30
    (240, 390) # 14:00 to 16:30
]

# Margaret does not want to meet on Monday
constraints.append(day == 1)

# Meeting must be within work hours
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Margaret's blocked times on Tuesday
for blocked_start, blocked_end in margaret_blocked_times_tuesday:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Alexis's blocked times on Tuesday
for blocked_start, blocked_end in alexis_blocked_times_tuesday:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Margaret's preference: meeting before 14:30
constraints.append(start_time + meeting_duration <= 330)  # 14:30 in minutes from 9:00

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long() + 9 * 60  # Convert to minutes from 00:00
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")