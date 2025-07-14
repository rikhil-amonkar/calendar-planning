from z3 import *

# Define the variables for the meeting day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Constants for the problem
meeting_duration = 30  # 30 minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the constraints for Bobby's schedule
bobby_busy_times = [
    (14 * 60 + 30, 15 * 60),  # Monday 14:30 - 15:00
    (9 * 60, 11 * 60 + 30),   # Tuesday 9:00 - 11:30
    (12 * 60, 12 * 60 + 30),  # Tuesday 12:00 - 12:30
    (13 * 60, 15 * 60),       # Tuesday 13:00 - 15:00
    (15 * 60 + 30, 17 * 60)   # Tuesday 15:30 - 17:00
]

# Define the constraints for Michael's schedule
michael_busy_times = [
    (9 * 60, 10 * 60),        # Monday 9:00 - 10:00
    (10 * 60 + 30, 13 * 60 + 30),  # Monday 10:30 - 13:30
    (14 * 60, 15 * 60),       # Monday 14:00 - 15:00
    (15 * 60 + 30, 17 * 60),   # Monday 15:30 - 17:00
    (9 * 60, 10 * 60 + 30),   # Tuesday 9:00 - 10:30
    (11 * 60, 11 * 60 + 30),  # Tuesday 11:00 - 11:30
    (12 * 60, 14 * 60),       # Tuesday 12:00 - 14:00
    (15 * 60, 16 * 60),       # Tuesday 15:00 - 16:00
    (16 * 60 + 30, 17 * 60)   # Tuesday 16:30 - 17:00
]

# Create a solver instance
solver = Solver()

# Add constraints for the meeting day and time
solver.add(day >= 0, day <= 1)
solver.add(start_time >= work_start, start_time <= work_end - meeting_duration)

# Add constraints for Bobby's busy times
for busy_start, busy_end in bobby_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add constraints for Michael's busy times
for busy_start, busy_end in michael_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time_minutes = model[start_time].as_long()
    meeting_start_time = f"{(meeting_start_time_minutes // 60):02}:{(meeting_start_time_minutes % 60):02}"
    meeting_end_time_minutes = meeting_start_time_minutes + meeting_duration
    meeting_end_time = f"{(meeting_end_time_minutes // 60):02}:{(meeting_end_time_minutes % 60):02}"
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")