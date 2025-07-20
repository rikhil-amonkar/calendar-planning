from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00, which is 480 minutes from 9:00
work_start = 0  # 9:00 in minutes from 9:00
work_end = 480  # 17:00 in minutes from 9:00

# Shirley's blocked times
shirley_blocked_times = [
    (30, 60),  # 10:30 to 11:00
    (120, 150),  # 12:00 to 12:30
    (420, 450)  # 16:00 to 16:30
]

# Albert's blocked times
albert_blocked_times = [
    (0, 480),  # 9:00 to 17:00 on Monday
    (60, 90),  # 9:30 to 10:00 on Tuesday
    (150, 180),  # 11:30 to 12:30 on Tuesday
    (240, 360),  # 13:00 to 16:00 on Tuesday
    (450, 480)  # 16:30 to 17:00 on Tuesday
]

# Shirley's preference: not after 10:30 on Tuesday
shirley_preference = Or(day == 0, start_time <= 60)

# Define the solver
solver = Solver()

# Add constraints to the solver
solver.add(day >= 0, day <= 1)  # day can only be 0 (Monday) or 1 (Tuesday)
solver.add(start_time >= work_start, start_time + meeting_duration <= work_end)  # meeting must be within work hours
solver.add(shirley_preference)  # Shirley's preference

# Add Shirley's blocked times
for blocked_start, blocked_end in shirley_blocked_times:
    solver.add(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add Albert's blocked times
for blocked_start, blocked_end in albert_blocked_times:
    solver.add(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_time_formatted = f"{9 + meeting_start_time // 60}:{meeting_start_time % 60:02}"
    meeting_end_time_formatted = f"{9 + (meeting_start_time + meeting_duration) // 60}:{(meeting_start_time + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time_formatted}\nEnd Time: {meeting_end_time_formatted}")
else:
    print("No solution found")