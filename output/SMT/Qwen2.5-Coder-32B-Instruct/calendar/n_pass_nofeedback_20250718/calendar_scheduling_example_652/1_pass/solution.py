from z3 import *

# Define the variables for the meeting day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = 540
work_end = 1020

# Jesse's schedule
jesse_busy_times = [
    (0, 810, 840),  # Monday 13:30 to 14:00
    (0, 870, 900),  # Monday 14:30 to 15:00
    (1, 540, 570),  # Tuesday 9:00 to 9:30
    (1, 780, 810),  # Tuesday 13:00 to 13:30
    (1, 840, 900)   # Tuesday 14:00 to 15:00
]

# Lawrence's schedule
lawrence_busy_times = [
    (0, 540, 1020),  # Monday 9:00 to 17:00
    (1, 570, 630),   # Tuesday 9:30 to 10:30
    (1, 690, 750),   # Tuesday 11:30 to 12:30
    (1, 780, 810),   # Tuesday 13:00 to 13:30
    (1, 870, 900),   # Tuesday 14:30 to 15:00
    (1, 930, 990)    # Tuesday 15:30 to 16:30
]

# Add constraints for the meeting day and time
solver.add(day >= 0)
solver.add(day <= 1)
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints to avoid busy times
for d, s, e in jesse_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

for d, s, e in lawrence_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")