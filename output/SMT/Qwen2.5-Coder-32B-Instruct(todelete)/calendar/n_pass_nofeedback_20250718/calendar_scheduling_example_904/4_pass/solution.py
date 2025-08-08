from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Daniel's busy times
daniel_busy_times = [
    (30, 60), (60, 90), (180, 210), (270, 300), (330, 360),  # Monday
    (120, 150), (180, 210), (330, 360), (390, 480),  # Tuesday
    (0, 60), (240, 270),  # Wednesday
    (60, 90), (120, 150), (270, 300), (330, 360),  # Thursday
    (0, 30), (70, 120), (180, 210), (390, 480)  # Friday
]

# Bradley's busy times
bradley_busy_times = [
    (30, 120), (70, 120), (90, 180), (150, 240),  # Monday
    (60, 120), (90, 180), (150, 180), (240, 360),  # Tuesday
    (0, 60), (60, 180), (150, 180), (240, 480),  # Wednesday
    (0, 180), (90, 180), (150, 180), (240, 360),  # Thursday
    (0, 30), (0, 180), (180, 210), (240, 270), (330, 360)  # Friday
]

# Add constraints for work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Daniel's busy times
for d, (s, e) in enumerate(daniel_busy_times):
    day_index = d // 6
    solver.add(Or(day != day_index, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Bradley's busy times
for d, (s, e) in enumerate(bradley_busy_times):
    day_index = d // 6
    solver.add(Or(day != day_index, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for preferences
# Daniel would rather not meet on Wednesday or Thursday
solver.add(day != 2)
solver.add(day != 3)

# Bradley do not want to meet on Monday, Tuesday before 12:00, Friday
solver.add(day != 0)
solver.add(Or(day != 1, start_time >= 180))  # 12:00 in minutes from 9:00
solver.add(day != 4)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    if 0 <= day_value < len(days):
        day_str = days[day_value]
    else:
        raise ValueError("Invalid day value")

    # Convert time from minutes to HH:MM format
    start_time_str = f"{(start_time_value // 60) + 9:02}:{start_time_value % 60:02}"
    end_time_str = f"{(end_time_value // 60) + 9:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")
    print("Constraints:")
    for c in solver.assertions():
        print(c)