from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Define the work hours in minutes from 9:00
work_start = 0  # 9:00
work_end = 480  # 17:00

# Meeting duration in minutes
meeting_duration = 30

# Susan's blocked times
susan_blocked_times = [
    (180, 210),  # Monday 12:30 to 13:00
    (210, 240),  # Monday 13:30 to 14:00
    (390, 420),  # Tuesday 11:30 to 12:00
    (0, 60),     # Wednesday 9:30 to 10:30
    (300, 315),  # Wednesday 14:00 to 14:30
    (390, 480)   # Wednesday 15:30 to 16:30
]

# Sandra's blocked times
sandra_blocked_times = [
    (0, 240),    # Monday 9:00 to 13:00
    (300, 360),  # Monday 14:00 to 15:00
    (420, 450),  # Monday 16:00 to 16:30
    (0, 30),     # Tuesday 9:00 to 9:30
    (60, 120),   # Tuesday 10:30 to 12:00
    (150, 210),  # Tuesday 12:30 to 13:30
    (300, 315),  # Tuesday 14:00 to 14:30
    (360, 480),  # Tuesday 16:00 to 17:00
    (0, 75),     # Wednesday 9:00 to 11:30
    (75, 90),    # Wednesday 12:00 to 12:30
    (90, 480)    # Wednesday 13:00 to 17:00
]

# Add constraints for the day
constraints.append(Or(day == 0, day == 1, day == 2))

# Add constraints for the start time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Add constraints for Susan's blocked times
for blocked_start, blocked_end in susan_blocked_times:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add constraints for Sandra's blocked times
for blocked_start, blocked_end in sandra_blocked_times:
    constraints.append(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Susan would rather not meet on Tuesday
constraints.append(day != 1)

# Sandra can not meet on Monday after 16:00
constraints.append(Or(day != 0, start_time + meeting_duration <= 360))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday"]
    meeting_day_str = days[meeting_day]

    # Convert time from minutes to HH:MM format
    meeting_start_time_str = f"{9 + meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_str = f"{9 + meeting_end_time // 60:02}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_time_str}\nEnd Time: {meeting_end_time_str}")
else:
    print("No solution found")