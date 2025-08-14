from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
solver.add(Or(day == 0, day == 1))
solver.add(start_time >= 540)
solver.add(start_time + meeting_duration <= 1020)

# Russell's busy times
solver.add(Or(day != 0, Or(start_time < 630, start_time >= 660)))  # Monday 10:30 to 11:00
solver.add(Or(day != 1, Or(start_time < 780, start_time >= 810)))  # Tuesday 13:00 to 13:30

# Alexander's busy times
solver.add(Or(day != 0, Or(start_time < 540, start_time >= 690)))  # Monday 9:00 to 11:30
solver.add(Or(day != 0, Or(start_time < 720, start_time >= 870)))  # Monday 12:00 to 14:30
solver.add(Or(day != 0, Or(start_time < 900, start_time >= 1020)))  # Monday 15:00 to 17:00
solver.add(Or(day != 1, Or(start_time < 540, start_time >= 600)))  # Tuesday 9:00 to 10:00
solver.add(Or(day != 1, Or(start_time < 780, start_time >= 840)))  # Tuesday 13:00 to 14:00
solver.add(Or(day != 1, Or(start_time < 900, start_time >= 930)))  # Tuesday 15:00 to 15:30
solver.add(Or(day != 1, Or(start_time < 960, start_time >= 990)))  # Tuesday 16:00 to 16:30

# Russell's preference: not before 13:30 on Tuesday
solver.add(Or(day != 1, start_time >= 810))  # Tuesday 13:30 in minutes

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_time_formatted = f"{meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_formatted = f"{(meeting_start_time + meeting_duration) // 60:02}:{(meeting_start_time + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time_formatted}\nEnd Time: {meeting_end_time_formatted}")
else:
    print("No solution found")