from z3 import *

# Define the variables for the meeting day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
solver.add(Or(day == 0, day == 1))
solver.add(start_time >= 540)
solver.add(start_time + meeting_duration <= 1020)

# Bobby's busy times
# Monday: 14:30 to 15:00 (870 to 900 minutes)
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 870, start_time >= 900)))
# Tuesday: 9:00 to 11:30 (540 to 690 minutes), 12:00 to 12:30 (720 to 750 minutes), 13:00 to 15:00 (780 to 900 minutes), 15:30 to 17:00 (930 to 1020 minutes)
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 540, start_time >= 690)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 720, start_time >= 750)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 780, start_time >= 900)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 930, start_time >= 1020)))

# Michael's busy times
# Monday: 9:00 to 10:00 (540 to 600 minutes), 10:30 to 13:30 (630 to 810 minutes), 14:00 to 15:00 (840 to 900 minutes), 15:30 to 17:00 (930 to 1020 minutes)
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 540, start_time >= 600)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 630, start_time >= 810)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 840, start_time >= 900)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 930, start_time >= 1020)))
# Tuesday: 9:00 to 10:30 (540 to 630 minutes), 11:00 to 11:30 (660 to 690 minutes), 12:00 to 14:00 (720 to 840 minutes), 15:00 to 16:00 (900 to 960 minutes), 16:30 to 17:00 (990 to 1020 minutes)
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 540, start_time >= 630)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 660, start_time >= 690)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 720, start_time >= 840)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 900, start_time >= 960)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 990, start_time >= 1020)))

# Check if there is a solution
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