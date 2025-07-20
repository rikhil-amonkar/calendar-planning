from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Carl's busy times
carl_busy_times = [
    (0, 11 * 60, 11 * 60 + 30),  # Monday 11:00 to 11:30
    (1, 14 * 60 + 30, 15 * 60),  # Tuesday 14:30 to 15:00
    (2, 10 * 60, 11 * 60 + 30),  # Wednesday 10:00 to 11:30
    (2, 13 * 60, 13 * 60 + 30),  # Wednesday 13:00 to 13:30
    (3, 13 * 60 + 30, 14 * 60),  # Thursday 13:30 to 14:00
    (3, 16 * 60, 16 * 60 + 30)   # Thursday 16:00 to 16:30
]

# Margaret's busy times
margaret_busy_times = [
    (0, 9 * 60, 10 * 60 + 30),  # Monday 9:00 to 10:30
    (0, 11 * 60, 17 * 60),      # Monday 11:00 to 17:00
    (1, 9 * 60 + 30, 12 * 60),  # Tuesday 9:30 to 12:00
    (1, 13 * 60 + 30, 14 * 60), # Tuesday 13:30 to 14:00
    (1, 15 * 60 + 30, 17 * 60), # Tuesday 15:30 to 17:00
    (2, 9 * 60 + 30, 12 * 60),  # Wednesday 9:30 to 12:00
    (2, 12 * 60 + 30, 13 * 60), # Wednesday 12:30 to 13:00
    (2, 13 * 60 + 30, 14 * 60 + 30), # Wednesday 13:30 to 14:30
    (2, 15 * 60, 17 * 60),      # Wednesday 15:00 to 17:00
    (3, 10 * 60, 12 * 60),      # Thursday 10:00 to 12:00
    (3, 12 * 60 + 30, 14 * 60), # Thursday 12:30 to 14:00
    (3, 14 * 60 + 30, 17 * 60)  # Thursday 14:30 to 17:00
]

# Constraints for the day
solver.add(day >= 0)
solver.add(day <= 3)

# Constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Carl's busy times constraints
for d, s, e in carl_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Margaret's busy times constraints
for d, s, e in margaret_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Carl's preference to avoid Thursday
solver.add(day != 3)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday", "Thursday"][model[day].as_long()]
    meeting_start_time = model[start_time].as_long()
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")