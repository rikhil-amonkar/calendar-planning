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
    (540, 570),  # 9:00 to 9:30 on Tuesday
    (600, 630),  # 10:00 to 10:30 on Tuesday
    (690, 720),  # 11:30 to 12:00 on Tuesday
    (810, 870),  # 13:30 to 14:30 on Tuesday
    (930, 990),  # 15:30 to 16:00 on Tuesday
    (990, 1020)  # 16:30 to 17:00 on Tuesday
]

# Nathan's busy times
nathan_busy_times = [
    (600, 630),  # 10:00 to 10:30
    (660, 690),  # 11:00 to 11:30
    (810, 870),  # 13:30 to 14:30
    (960, 990),  # 16:00 to 16:30
    (540, 630),  # 9:00 to 10:30 on Tuesday
    (660, 780),  # 11:00 to 13:00 on Tuesday
    (810, 840),  # 13:30 to 14:00 on Tuesday
    (870, 930),  # 14:30 to 15:30 on Tuesday
    (960, 990)   # 16:00 to 16:30 on Tuesday
]

# Amanda's preference: no meeting on Tuesday after 11:00
amanda_preference = Or(day == 0, start_time <= 660)

# Nathan's preference: no meeting on Monday
nathan_preference = day == 1

# Create the solver
solver = Solver()

# Add constraints for work hours
solver.add(Or(day == 0, day == 1))
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Amanda's busy times
for busy_start, busy_end in amanda_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add constraints for Nathan's busy times
for busy_start, busy_end in nathan_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add preferences
solver.add(amanda_preference)
solver.add(nathan_preference)

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