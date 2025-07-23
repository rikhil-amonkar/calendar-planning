from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the days
solver.add(day >= 0)
solver.add(day <= 4)

# Define the start time within work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Eugene's busy times
eugene_busy_times = [
    (0, 11 * 60, 12 * 60),  # Monday 11:00 to 12:00
    (0, 13 * 60 + 30, 14 * 60),  # Monday 13:30 to 14:00
    (0, 14 * 60 + 30, 15 * 60),  # Monday 14:30 to 15:00
    (0, 16 * 60, 16 * 60 + 30),  # Monday 16:00 to 16:30
    (2, 9 * 60, 9 * 60 + 30),  # Wednesday 9:00 to 9:30
    (2, 11 * 60, 11 * 60 + 30),  # Wednesday 11:00 to 11:30
    (2, 12 * 60, 12 * 60 + 30),  # Wednesday 12:00 to 12:30
    (2, 13 * 60 + 30, 15 * 60),  # Wednesday 13:30 to 15:00
    (3, 9 * 60 + 30, 10 * 60),  # Thursday 9:30 to 10:00
    (3, 11 * 60, 12 * 60 + 30),  # Thursday 11:00 to 12:30
    (4, 10 * 60 + 30, 11 * 60),  # Friday 10:30 to 11:00
    (4, 12 * 60, 12 * 60 + 30),  # Friday 12:00 to 12:30
    (4, 13 * 60, 13 * 60 + 30)  # Friday 13:00 to 13:30
]

# Eric's busy times
eric_busy_times = [
    (0, 9 * 60, 17 * 60),  # Monday 9:00 to 17:00
    (1, 9 * 60, 17 * 60),  # Tuesday 9:00 to 17:00
    (2, 9 * 60, 11 * 60 + 30),  # Wednesday 9:00 to 11:30
    (2, 12 * 60, 14 * 60),  # Wednesday 12:00 to 14:00
    (2, 14 * 60 + 30, 16 * 60 + 30),  # Wednesday 14:30 to 16:30
    (3, 9 * 60, 17 * 60),  # Thursday 9:00 to 17:00
    (4, 9 * 60, 11 * 60),  # Friday 9:00 to 11:00
    (4, 11 * 60 + 30, 17 * 60)  # Friday 11:30 to 17:00
]

# Add constraints for Eugene's busy times
for d, s, e in eugene_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Eric's busy times
for d, s, e in eric_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Eric would like to avoid more meetings on Wednesday
solver.add(day != 2)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[day_value]

    # Convert time from minutes to HH:MM format
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")