from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # Start time in minutes since 9:00

# Constants for the problem
meeting_duration = 30  # Meeting duration in minutes
work_start = 0  # 9:00 in minutes since 9:00
work_end = 480  # 17:00 in minutes since 9:00

# Jean's busy times
jean_busy_times = [
    (11*60 + 30, 12*60),  # 11:30 to 12:00
    (16*60, 16*60 + 30)   # 16:00 to 16:30
]

# Doris's busy times
doris_busy_times = [
    (0, 11*60 + 30),  # 9:00 to 11:30
    (12*60, 12*60 + 30),  # 12:00 to 12:30
    (13*60 + 30, 16*60),  # 13:30 to 16:00
    (16*60 + 30, 17*60)   # 16:30 to 17:00
]

# Doris's preference
doris_preferred_end = 14*60  # Prefer not to meet after 14:00 on Monday

# Create the solver
solver = Solver()

# Constraints for the day
solver.add(Or(day == 0, day == 1))

# Constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Constraints to avoid Jean's busy times
for busy_start, busy_end in jean_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Constraints to avoid Doris's busy times
for busy_start, busy_end in doris_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Doris's preference constraint
solver.add(Implies(day == 0, start_time + meeting_duration <= doris_preferred_end))

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