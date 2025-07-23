from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Work hours are from 9:00 to 17:00 (0 to 480 minutes from 9:00)
solver.add(Or(day == 0, day == 1))
solver.add(start_time >= 0)
solver.add(start_time + meeting_duration <= 480)  # 480 minutes is 17:00 from 9:00

# Patricia's schedule
# Monday: 10:00 to 10:30, 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:30, 16:00 to 16:30
# Tuesday: 10:00 to 10:30, 11:00 to 12:00, 14:00 to 16:00, 16:30 to 17:00
solver.add(Or(
    day == 1,  # Tuesday
    Or(
        start_time + meeting_duration <= 60,  # before 10:00
        start_time >= 90,  # after 10:30
        start_time + meeting_duration <= 150,  # before 11:30
        start_time >= 180,  # after 12:00
        start_time + meeting_duration <= 270,  # before 13:30
        start_time >= 360,  # after 14:30
        start_time + meeting_duration <= 390  # before 15:30
    )
))

# Jesse's schedule
# Monday: 9:00 to 17:00 (all day)
# Tuesday: 11:00 to 11:30, 12:00 to 12:30, 13:00 to 14:00, 14:30 to 15:00, 15:30 to 17:00
solver.add(Or(
    day == 0,  # Monday (all day)
    Or(
        start_time + meeting_duration <= 60,  # before 11:00
        start_time >= 90,  # after 11:30
        start_time + meeting_duration <= 120,  # before 12:00
        start_time >= 150,  # after 12:30
        start_time + meeting_duration <= 180,  # before 13:00
        start_time >= 210,  # after 14:00
        start_time + meeting_duration <= 240,  # before 14:30
        start_time >= 270,  # after 15:00
        start_time + meeting_duration <= 330,  # before 15:30
        start_time >= 390  # after 16:30
    )
))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    day_str = "Monday" if day_value == 0 else "Tuesday"
    start_time_str = f"{9 + start_time_value // 60}:{start_time_value % 60:02}"
    end_time_str = f"{9 + (start_time_value + meeting_duration) // 60}:{(start_time_value + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")