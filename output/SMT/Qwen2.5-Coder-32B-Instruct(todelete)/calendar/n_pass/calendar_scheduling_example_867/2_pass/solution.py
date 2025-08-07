from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Define the meeting duration in minutes
meeting_duration = 30

# Betty's busy times
betty_busy_times = [
    (60, 90), (270, 300), (300, 330), (360, 390),  # Monday
    (0, 30), (75, 120), (150, 180), (270, 300), (390, 480),  # Tuesday
    (30, 60), (210, 240), (240, 270),  # Wednesday
    (30, 60), (75, 120), (240, 270), (300, 330), (390, 480)  # Thursday
]

# Scott's busy times
scott_busy_times = [
    (30, 900), (930, 990), (1020, 1050),  # Monday
    (0, 30), (60, 120), (75, 120), (150, 180), (240, 300), (960, 1020),  # Tuesday
    (30, 180), (210, 240), (240, 270), (300, 330), (960, 1020),  # Wednesday
    (0, 30), (60, 90), (120, 150), (150, 180), (900, 960)  # Thursday
]

# Add constraints for Betty's busy times
for d, (s, e) in enumerate(betty_busy_times):
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Scott's busy times
for d, (s, e) in enumerate(scott_busy_times):
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Betty can not meet on Monday
constraints.append(day != 0)

# Tuesday is not an option
constraints.append(day != 1)

# Thursday before 15:00 is not an option
constraints.append(Or(day != 3, start_time >= 360))

# Scott would like to avoid more meetings on Wednesday
# We can add a soft constraint by penalizing Wednesday, but since we need a hard solution, we just avoid it if possible
constraints.append(day != 2)

# Define the solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    if 0 <= meeting_day < len(days):
        meeting_day_str = days[meeting_day]
    else:
        meeting_day_str = "Invalid Day"

    # Convert start and end times to HH:MM format
    start_hour = 9 + meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = 9 + meeting_end_time // 60
    end_minute = meeting_end_time % 60

    start_time_str = f"{start_hour:02}:{start_minute:02}"
    end_time_str = f"{end_hour:02}:{end_minute:02}"

    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")