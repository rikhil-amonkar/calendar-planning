from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
solver.add(start_time >= 540)
solver.add(start_time + meeting_duration <= 1020)

# John's constraints: No meetings on Monday after 14:30 (870 minutes)
solver.add(Or(day != 0, start_time + meeting_duration <= 870))

# Jennifer's constraints
# Monday: 9:00 to 11:00 (540 to 660), 11:30 to 13:00 (690 to 780), 13:30 to 14:30 (810 to 870), 15:00 to 17:00 (900 to 1020)
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 540, start_time >= 660)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 690, start_time >= 780)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 810, start_time >= 870)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 900, start_time >= 1020)))

# Tuesday: 9:00 to 11:30 (540 to 690), 12:00 to 17:00 (720 to 1020)
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 540, start_time >= 690)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 720, start_time >= 1020)))

# Wednesday: 9:00 to 11:30 (540 to 690), 12:00 to 12:30 (720 to 750), 13:00 to 14:00 (780 to 840), 14:30 to 16:00 (870 to 960), 16:30 to 17:00 (990 to 1020)
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 540, start_time >= 690)))
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 720, start_time >= 750)))
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 780, start_time >= 840)))
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 870, start_time >= 960)))
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 990, start_time >= 1020)))

# Additional constraint to avoid 16:00 to 16:30 on Wednesday
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 960, start_time >= 990)))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")