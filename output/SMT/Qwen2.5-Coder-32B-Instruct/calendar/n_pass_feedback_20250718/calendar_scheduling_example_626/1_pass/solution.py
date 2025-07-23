from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Work hours are from 9:00 to 17:00 (480 to 1020 minutes from 9:00)
solver.add(Or(day == 0, day == 1))
solver.add(start_time >= 0)
solver.add(start_time + meeting_duration <= 720)  # 720 minutes is 12:00 PM, but we are considering up to 17:00 (840 minutes from 9:00)

# Patricia's schedule
# Monday: 10:00 to 10:30, 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:30, 16:00 to 16:30
# Tuesday: 10:00 to 10:30, 11:00 to 12:00, 14:00 to 16:00, 16:30 to 17:00
solver.add(Or(day == 1, Or(start_time + meeting_duration <= 60, start_time >= 90, start_time + meeting_duration <= 150, start_time >= 180, start_time + meeting_duration <= 270, start_time >= 360, start_time + meeting_duration <= 390)))

# Jesse's schedule
# Monday: 9:00 to 17:00 (all day)
# Tuesday: 11:00 to 11:30, 12:00 to 12:30, 13:00 to 14:00, 14:30 to 15:00, 15:30 to 17:00
solver.add(Or(day == 0, Or(start_time + meeting_duration <= 120, start_time >= 150, start_time + meeting_duration <= 180, start_time >= 210, start_time + meeting_duration <= 240, start_time >= 270, start_time + meeting_duration <= 300, start_time >= 390)))

# Solve the problem
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

    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_time:02}:{meeting_end_minute:02}")
else:
    print("No solution found")