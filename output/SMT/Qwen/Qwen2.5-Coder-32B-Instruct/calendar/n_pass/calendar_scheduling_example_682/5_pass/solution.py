from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (0 to 480 minutes from 9:00)
work_start = 0  # 9:00 in minutes from 9:00
work_end = 480  # 17:00 in minutes from 9:00

# Amanda's schedule
amanda_busy_times = [
    (0, 0, 84),   # Monday 9:00 to 10:30
    (0, 60, 90),  # Monday 11:00 to 11:30
    (0, 180, 210), # Monday 12:30 to 13:00
    (0, 240, 270), # Monday 13:30 to 14:00
    (0, 300, 330), # Monday 14:30 to 15:00
    (1, 0, 30),   # Tuesday 9:00 to 9:30
    (1, 60, 90),  # Tuesday 10:00 to 10:30
    (1, 120, 150), # Tuesday 11:30 to 12:00
    (1, 240, 300), # Tuesday 13:30 to 14:30
    (1, 360, 420), # Tuesday 15:30 to 16:00
    (1, 420, 480)  # Tuesday 16:30 to 17:00
]

# Nathan's schedule
nathan_busy_times = [
    (0, 60, 90),  # Monday 10:00 to 10:30
    (0, 120, 150), # Monday 11:00 to 11:30
    (0, 240, 300), # Monday 13:30 to 14:30
    (0, 360, 390), # Monday 16:00 to 16:30
    (1, 0, 90),   # Tuesday 9:00 to 10:30
    (1, 60, 180), # Tuesday 11:00 to 13:00
    (1, 240, 270), # Tuesday 13:30 to 14:00
    (1, 300, 360), # Tuesday 14:30 to 15:30
    (1, 360, 390)  # Tuesday 16:00 to 16:30
]

# Add constraints for the day
constraints.append(Or(day == 0, day == 1))

# Add constraints for the time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Add constraints for Amanda's busy times
for d, s, e in amanda_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Nathan's busy times
for d, s, e in nathan_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Amanda does not want to meet on Tuesday after 11:00
constraints.append(Or(day != 1, start_time + meeting_duration <= 120))  # 120 minutes is 11:00 in minutes from 9:00

# Nathan cannot meet on Monday
constraints.append(day != 0)

# Manually define the available slots on Tuesday
available_slots = [(1, 30, 60)]  # Tuesday 9:30 to 10:00

# Add constraints for the available slots
for d, s, e in available_slots:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long() + 540  # Convert minutes from 9:00 to actual time
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")