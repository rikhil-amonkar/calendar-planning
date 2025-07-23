from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
constraints.append(start_time >= 540)
constraints.append(start_time + meeting_duration <= 1020)

# Joshua's schedule
# Monday: 15:00 to 15:30 (900 to 930 minutes)
constraints.append(Or(day != 0, Or(start_time + meeting_duration <= 900, start_time >= 930)))
# Tuesday: 11:30 to 12:00 (690 to 720 minutes), 13:00 to 13:30 (780 to 810 minutes), 14:30 to 15:00 (870 to 900 minutes)
constraints.append(Or(day != 1, Or(start_time + meeting_duration <= 690, start_time >= 720)))
constraints.append(Or(day != 1, Or(start_time + meeting_duration <= 780, start_time >= 810)))
constraints.append(Or(day != 1, Or(start_time + meeting_duration <= 870, start_time >= 900)))

# Joyce's schedule
# Monday: 9:00 to 9:30 (540 to 570 minutes), 10:00 to 11:00 (600 to 660 minutes), 11:30 to 12:30 (690 to 750 minutes), 13:00 to 15:00 (780 to 900 minutes), 15:30 to 17:00 (930 to 1020 minutes)
constraints.append(Or(day != 0, Or(start_time + meeting_duration <= 540, start_time >= 570)))
constraints.append(Or(day != 0, Or(start_time + meeting_duration <= 600, start_time >= 660)))
constraints.append(Or(day != 0, Or(start_time + meeting_duration <= 690, start_time >= 750)))
constraints.append(Or(day != 0, Or(start_time + meeting_duration <= 780, start_time >= 900)))
constraints.append(Or(day != 0, Or(start_time + meeting_duration <= 930, start_time >= 1020)))
# Tuesday: 9:00 to 17:00 (540 to 1020 minutes)
constraints.append(Or(day != 1, Or(start_time + meeting_duration <= 540, start_time >= 1020)))
# Wednesday: 9:00 to 9:30 (540 to 570 minutes), 10:00 to 11:00 (600 to 660 minutes), 12:30 to 15:30 (750 to 930 minutes), 16:00 to 16:30 (960 to 990 minutes)
constraints.append(Or(day != 2, Or(start_time + meeting_duration <= 540, start_time >= 570)))
constraints.append(Or(day != 2, Or(start_time + meeting_duration <= 600, start_time >= 660)))
constraints.append(Or(day != 2, Or(start_time + meeting_duration <= 750, start_time >= 930)))
constraints.append(Or(day != 2, Or(start_time + meeting_duration <= 960, start_time >= 990)))

# Joyce's preference: not before 12:00 on Monday
constraints.append(Or(day != 0, start_time >= 720))

# Solve the problem
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    day_str = ["Monday", "Tuesday", "Wednesday"][day_value]
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")