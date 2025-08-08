from z3 import *

# Define the variables for the meeting day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Define the work hours in minutes from 9:00
work_start = 0  # 9:00
work_end = 480  # 17:00

# Patricia's schedule in minutes from 9:00
patricia_busy = [
    (60, 90),  # 10:00 to 10:30
    (150, 180),  # 11:30 to 12:00
    (240, 270),  # 13:00 to 13:30
    (330, 390),  # 14:30 to 15:30
    (420, 450)  # 16:00 to 16:30
]

# Patricia's schedule on Tuesday
patricia_busy_tuesday = [
    (60, 90),  # 10:00 to 10:30
    (60, 180),  # 11:00 to 12:00
    (240, 360),  # 14:00 to 16:00
    (390, 480)  # 16:30 to 17:00
]

# Jesse's schedule in minutes from 9:00
jesse_busy = [
    (0, 480)  # 9:00 to 17:00 on Monday
]

# Jesse's schedule on Tuesday
jesse_busy_tuesday = [
    (120, 150),  # 11:00 to 11:30
    (180, 210),  # 12:00 to 12:30
    (240, 270),  # 13:00 to 14:00
    (330, 390),  # 14:30 to 15:00
    (390, 480)  # 15:30 to 17:00
]

# Constraints for the day
solver.add(Or(day == 0, day == 1))

# Constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Constraints for Patricia's availability
for busy_start, busy_end in patricia_busy:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Constraints for Patricia's availability on Tuesday
for busy_start, busy_end in patricia_busy_tuesday:
    solver.add(Or(And(day == 1, start_time + meeting_duration <= busy_start), And(day == 1, start_time >= busy_end)))

# Constraints for Jesse's availability
for busy_start, busy_end in jesse_busy:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Constraints for Jesse's availability on Tuesday
for busy_start, busy_end in jesse_busy_tuesday:
    solver.add(Or(And(day == 1, start_time + meeting_duration <= busy_start), And(day == 1, start_time >= busy_end)))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_hour = meeting_start_time // 60 + 9
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60 + 9
    meeting_end_minute = meeting_end_time % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")