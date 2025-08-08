from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Define the work hours
solver.add(day >= 0)
solver.add(day <= 4)
solver.add(start_time >= 0)
solver.add(start_time <= 480)  # 480 minutes is 8 hours (from 9:00 to 17:00)

# Define Diane's busy times
diane_busy_times = [
    (0, 720, 750),  # Monday 12:00 to 12:30
    (0, 900, 930),  # Monday 15:00 to 15:30
    (1, 600, 660),  # Tuesday 10:00 to 11:00
    (1, 690, 720),  # Tuesday 11:30 to 12:00
    (1, 750, 780),  # Tuesday 12:30 to 13:00
    (1, 960, 1020), # Tuesday 16:00 to 17:00
    (2, 0, 30),     # Wednesday 9:00 to 9:30
    (2, 870, 900),  # Wednesday 14:30 to 15:00
    (2, 990, 1050), # Wednesday 16:30 to 17:00
    (3, 930, 990),  # Thursday 15:30 to 16:30
    (4, 30, 690),   # Friday 9:30 to 11:30
    (4, 870, 900),  # Friday 14:30 to 15:00
    (4, 960, 1020)  # Friday 16:00 to 17:00
]

# Define Matthew's busy times
matthew_busy_times = [
    (0, 0, 60),     # Monday 9:00 to 10:00
    (0, 630, 1020), # Monday 10:30 to 17:00
    (1, 0, 1020),   # Tuesday 9:00 to 17:00
    (2, 0, 660),    # Wednesday 9:00 to 11:00
    (2, 720, 870),  # Wednesday 12:00 to 14:30
    (2, 960, 1020), # Wednesday 16:00 to 17:00
    (3, 0, 960),    # Thursday 9:00 to 16:00
    (4, 0, 1020)    # Friday 9:00 to 17:00
]

# Add constraints for Diane's busy times
for d, s, e in diane_busy_times:
    solver.add(Or(day != d, Or(start_time >= e, start_time + 60 <= s)))

# Add constraints for Matthew's busy times
for d, s, e in matthew_busy_times:
    solver.add(Or(day != d, Or(start_time >= e, start_time + 60 <= s)))

# Matthew's preference: not before 12:30 on Wednesday
solver.add(Or(day != 2, start_time >= 180))  # 180 minutes is 12:30

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 60

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[day_value]

    # Convert start and end times to HH:MM format
    start_time_str = f"{9 + start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")