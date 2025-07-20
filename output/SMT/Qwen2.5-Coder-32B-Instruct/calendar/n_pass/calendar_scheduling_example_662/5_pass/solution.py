from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
meeting_duration = 60  # 1 hour meeting

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = 540
work_end = 1020

# Gary's blocked times
gary_blocked_times = [
    (570, 600),  # Monday 9:30 to 10:00
    (660, 780),  # Monday 11:00 to 13:00
    (840, 870),  # Monday 14:00 to 14:30
    (990, 1020), # Monday 16:30 to 17:00
    (540, 570),  # Tuesday 9:00 to 9:30
    (630, 660),  # Tuesday 10:30 to 11:00
    (870, 960)   # Tuesday 14:30 to 16:00
]

# David's blocked times
david_blocked_times = [
    (540, 570),  # Monday 9:00 to 9:30
    (570, 780),  # Monday 10:00 to 13:00
    (870, 990),  # Monday 14:30 to 16:30
    (540, 570),  # Tuesday 9:00 to 9:30
    (570, 630),  # Tuesday 10:00 to 10:30
    (630, 750),  # Tuesday 11:00 to 12:30
    (780, 870),  # Tuesday 13:00 to 14:30
    (900, 960),  # Tuesday 15:00 to 16:00
    (990, 1020)  # Tuesday 16:30 to 17:00
]

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(Or(day == 0, day == 1))

# Add constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Gary's blocked times
for blocked_start, blocked_end in gary_blocked_times:
    solver.add(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add constraints for David's blocked times
for blocked_start, blocked_end in david_blocked_times:
    solver.add(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

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