from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
meeting_duration = 30  # 30 minutes

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = 540
work_end = 1020

# Amanda's busy times
amanda_busy_times = [
    (540, 630),  # 9:00 to 10:30
    (660, 690),  # 11:00 to 11:30
    (750, 780),  # 12:30 to 13:00
    (810, 840),  # 13:30 to 14:00
    (870, 900),  # 14:30 to 15:00
    (1080, 1110),  # 9:00 to 9:30 on Tuesday
    (1140, 1170),  # 10:00 to 10:30 on Tuesday
    (1290, 1320),  # 11:30 to 12:00 on Tuesday
    (1620, 1710),  # 13:30 to 14:30 on Tuesday
    (1830, 1920),  # 15:30 to 16:00 on Tuesday
    (1980, 2070)  # 16:30 to 17:00 on Tuesday
]

# Nathan's busy times
nathan_busy_times = [
    (600, 630),  # 10:00 to 10:30
    (660, 690),  # 11:00 to 11:30
    (1620, 1710),  # 13:30 to 14:30
    (1920, 1950),  # 16:00 to 16:30
    (1080, 1110),  # 9:00 to 10:30 on Tuesday
    (1140, 1380),  # 10:00 to 13:00 on Tuesday
    (1620, 1680),  # 13:30 to 14:00 on Tuesday
    (1710, 1830),  # 14:30 to 15:30 on Tuesday
    (1920, 1950)  # 16:00 to 16:30 on Tuesday
]

# Amanda's preference: no meeting on Tuesday after 11:00
amanda_preference = Or(day == 0, start_time <= 660)

# Nathan's preference: no meeting on Monday
nathan_preference = day == 1

# Create the solver
solver = Solver()

# Add constraints
solver.add(day >= 0, day <= 1)  # day can only be 0 (Monday) or 1 (Tuesday)
solver.add(start_time >= work_start, start_time + meeting_duration <= work_end)  # meeting within work hours
solver.add(amanda_preference)
solver.add(nathan_preference)

# Add busy times constraints
for busy_start, busy_end in amanda_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

for busy_start, busy_end in nathan_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check if the constraints are satisfiable
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