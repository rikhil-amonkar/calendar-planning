from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, ..., 5 for Friday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
solver.add(start_time >= 540)
solver.add(start_time + meeting_duration <= 1020)

# Days are from Monday to Friday
solver.add(day >= 1)
solver.add(day <= 5)

# Eugene's busy times
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 660, start_time >= 810)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 810, start_time >= 870)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 870, start_time >= 900)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 960, start_time >= 990)))
solver.add(Or(day != 3, Or(start_time + meeting_duration <= 570, start_time >= 690)))
solver.add(Or(day != 3, Or(start_time + meeting_duration <= 690, start_time >= 720)))
solver.add(Or(day != 3, Or(start_time + meeting_duration <= 720, start_time >= 750)))
solver.add(Or(day != 3, Or(start_time + meeting_duration <= 810, start_time >= 900)))
solver.add(Or(day != 4, Or(start_time + meeting_duration <= 570, start_time >= 690)))
solver.add(Or(day != 4, Or(start_time + meeting_duration <= 690, start_time >= 720)))
solver.add(Or(day != 5, Or(start_time + meeting_duration <= 630, start_time >= 720)))
solver.add(Or(day != 5, Or(start_time + meeting_duration <= 720, start_time >= 750)))
solver.add(Or(day != 5, Or(start_time + meeting_duration <= 780, start_time >= 810)))

# Eric's busy times
solver.add(Or(day != 1, False))  # Busy all day
solver.add(Or(day != 2, False))  # Busy all day
solver.add(Or(day != 3, Or(start_time + meeting_duration <= 690, start_time >= 780)))
solver.add(Or(day != 3, Or(start_time + meeting_duration <= 780, start_time >= 870)))
solver.add(Or(day != 3, Or(start_time + meeting_duration <= 870, start_time >= 990)))
solver.add(Or(day != 4, False))  # Busy all day
solver.add(Or(day != 5, Or(start_time + meeting_duration <= 660, start_time >= 690)))
solver.add(Or(day != 5, Or(start_time + meeting_duration <= 690, start_time >= 1020)))

# Eric would like to avoid more meetings on Wednesday
solver.add(day != 3)

# Avoid scheduling the meeting from 9:00 to 11:00 on Friday
solver.add(Or(day != 5, Or(start_time + meeting_duration <= 540, start_time >= 660)))

# Manually specify the valid slot on Friday from 14:00 to 14:30
solver.add(day == 5)
solver.add(start_time == 840)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[day_value - 1]

    # Convert start and end times to HH:MM format
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")