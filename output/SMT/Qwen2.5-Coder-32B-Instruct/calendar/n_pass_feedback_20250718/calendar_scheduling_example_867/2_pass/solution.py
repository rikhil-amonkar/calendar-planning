from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Meeting duration in minutes
meeting_duration = 30

# Betty's busy times
betty_busy_times = [
    (60, 90), (270, 300), (300, 330), (360, 390),  # Monday
    (0, 30), (75, 120), (150, 180), (210, 240), (390, 480),  # Tuesday
    (30, 60), (90, 120), (120, 150), (210, 240),  # Wednesday
    (30, 60), (75, 120), (120, 150), (180, 210), (390, 480)  # Thursday
]

# Scott's busy times
scott_busy_times = [
    (30, 900), (930, 990), (1020, 1050), (840, 900), (990, 1020), (1020, 1050), (1140, 1200), (1230, 1260), (900, 990), (1020, 1050),  # Monday
    (0, 30), (60, 120), (75, 120), (150, 180), (210, 240), (900, 990), (1020, 1050), (1050, 1080), (1140, 1200), (1230, 1260), (900, 990),  # Tuesday
    (30, 180), (90, 120), (120, 150), (180, 210), (900, 990), (1020, 1050), (1050, 1080), (1140, 1200), (1230, 1260), (900, 990),  # Wednesday
    (0, 30), (60, 120), (75, 120), (150, 180), (900, 990), (1020, 1050), (1050, 1080), (1140, 1200), (1230, 1260), (900, 990)  # Thursday
]

# Betty can't meet on Monday
constraints.append(day != 0)

# Scott would like to avoid more meetings on Wednesday
constraints.append(day != 2)

# Thursday before 15:00 is not allowed for Betty
constraints.append(Or(day != 3, start_time >= 360))

# Define the constraints for each day
for d in range(4):
    for start, end in betty_busy_times[d*5:(d+1)*5]:
        constraints.append(Or(day != d, start_time + meeting_duration <= start, start_time >= end))
    for start, end in scott_busy_times[d*5:(d+1)*5]:
        constraints.append(Or(day != d, start_time + meeting_duration <= start, start_time >= end))

# Define the constraints for the meeting time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    start_time_str = f"{9 + start_time_value // 60}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")