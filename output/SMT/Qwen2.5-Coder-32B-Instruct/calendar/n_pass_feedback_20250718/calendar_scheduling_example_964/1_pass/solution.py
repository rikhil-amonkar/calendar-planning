from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday, 4 for Thursday, 5 for Friday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
constraints = []

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
constraints.append(start_time >= 540)
constraints.append(start_time + 60 <= 1020)  # Meeting duration is 1 hour

# Betty's schedule
betty_busy = [
    (1, 600, 630),  # Monday 10:00 to 10:30
    (1, 690, 750),  # Monday 11:30 to 12:30
    (1, 960, 990),  # Monday 16:00 to 16:30
    (2, 570, 600),  # Tuesday 9:30 to 10:00
    (2, 630, 660),  # Tuesday 10:30 to 11:00
    (2, 720, 750),  # Tuesday 12:00 to 12:30
    (2, 810, 900),  # Tuesday 13:30 to 15:00
    (2, 990, 1020), # Tuesday 16:30 to 17:00
    (3, 810, 840),  # Wednesday 13:30 to 14:00
    (3, 870, 900),  # Wednesday 14:30 to 15:00
    (5, 540, 600),  # Friday 9:00 to 10:00
    (5, 690, 720),  # Friday 11:30 to 12:00
    (5, 750, 780),  # Friday 12:30 to 13:00
    (5, 870, 900)   # Friday 14:30 to 15:00
]

# Megan's schedule
megan_busy = [
    (1, 540, 1020), # Monday 9:00 to 17:00
    (2, 540, 570),  # Tuesday 9:00 to 9:30
    (2, 600, 630),  # Tuesday 10:00 to 10:30
    (2, 720, 840),  # Tuesday 12:00 to 14:00
    (2, 900, 930),  # Tuesday 15:00 to 15:30
    (2, 960, 990),  # Tuesday 16:00 to 16:30
    (3, 570, 630),  # Wednesday 9:30 to 10:30
    (3, 660, 690),  # Wednesday 11:00 to 11:30
    (3, 750, 780),  # Wednesday 12:30 to 13:00
    (3, 810, 870),  # Wednesday 13:30 to 14:30
    (3, 930, 1020), # Wednesday 15:30 to 17:00
    (4, 570, 630),  # Thursday 9:00 to 10:30
    (4, 690, 840),  # Thursday 11:30 to 14:00
    (4, 870, 900),  # Thursday 14:30 to 15:00
    (4, 930, 990),  # Thursday 15:30 to 16:30
    (5, 540, 1020)  # Friday 9:00 to 17:00
]

# Betty can't meet on Wednesday or Thursday
constraints.append(day != 3)
constraints.append(day != 4)

# Add constraints for Betty's busy times
for d, s, e in betty_busy:
    constraints.append(Or(day != d, Or(start_time + 60 <= s, start_time >= e)))

# Add constraints for Megan's busy times
for d, s, e in megan_busy:
    constraints.append(Or(day != d, Or(start_time + 60 <= s, start_time >= e)))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 60

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[day_value - 1]

    # Convert time from minutes to HH:MM format
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")