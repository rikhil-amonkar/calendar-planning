from z3 import *

# Define the variables
day = Int('day')  # 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
start_time = Int('start_time')  # in minutes since 9:00

# Define the constraints
constraints = []

# Valid days
constraints.append(day >= 0)
constraints.append(day <= 4)

# Valid start times (between 9:00 and 16:00, i.e., 0 to 420 minutes)
constraints.append(start_time >= 0)
constraints.append(start_time <= 420)

# Meeting duration is 60 minutes
meeting_duration = 60

# Bryan's constraints
bryan_busy_times = [
    (3, 30, 60),  # Thursday 9:30-10:00
    (3, 150, 180),  # Thursday 12:30-13:00
    (4, 60, 90),  # Friday 10:30-11:00
    (4, 840, 870)  # Friday 14:00-14:30
]
for d, s, e in bryan_busy_times:
    constraints.append(Or(start_time + meeting_duration <= s, start_time >= e))

# Nicholas's constraints
nicholas_busy_times = [
    (0, 150, 180),  # Monday 11:30-12:00
    (0, 180, 330),  # Monday 13:00-15:30
    (1, 0, 30),  # Tuesday 9:00-9:30
    (1, 60, 810),  # Tuesday 11:00-16:30
    (2, 0, 30),  # Wednesday 9:00-9:30
    (2, 60, 90),  # Wednesday 10:00-11:00
    (2, 150, 810),  # Wednesday 11:30-16:30
    (3, 60, 90),  # Thursday 10:30-11:30
    (3, 120, 150),  # Thursday 12:00-12:30
    (3, 900, 930),  # Thursday 15:00-15:30
    (3, 990, 1020),  # Thursday 16:30-17:00
    (4, 0, 90),  # Friday 9:00-10:30
    (4, 60, 90),  # Friday 11:00-12:00
    (4, 150, 870),  # Friday 12:30-14:30
    (4, 930, 960),  # Friday 15:30-16:00
    (4, 990, 1020)  # Friday 16:30-17:00
]
for d, s, e in nicholas_busy_times:
    constraints.append(Or(start_time + meeting_duration <= s, start_time >= e))

# Bryan prefers not to meet on Tuesday
constraints.append(day != 1)

# Nicholas prefers not to meet on Monday or Thursday
constraints.append(And(day != 0, day != 3))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()

    # Convert day and start time to human-readable format
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    start_hour = 9 + start_time_value // 60
    start_minute = start_time_value % 60
    end_hour = start_hour + meeting_duration // 60
    end_minute = start_minute + meeting_duration % 60
    if end_minute >= 60:
        end_hour += 1
        end_minute -= 60

    print(f"SOLUTION:\nDay: {days_of_week[day_value]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")