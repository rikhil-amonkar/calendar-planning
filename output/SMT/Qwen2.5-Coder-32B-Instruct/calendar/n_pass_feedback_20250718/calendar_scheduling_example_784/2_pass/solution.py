from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Work hours are from 9:00 to 17:00 (480 to 1020 minutes from 9:00)
solver.add(start_time >= 0)
solver.add(start_time + meeting_duration <= 480)  # 17:00 - 9:00 = 480 minutes

# Judith's constraints
# Monday: 12:00 to 12:30 (180 to 210 minutes from 9:00)
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 180, start_time >= 210)))

# Wednesday: 11:30 to 12:00 (150 to 180 minutes from 9:00)
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 150, start_time >= 180)))

# Timothy's constraints
# Monday: 9:30 to 10:00 (30 to 60 minutes from 9:00), 10:30 to 11:30 (90 to 150 minutes from 9:00),
#         12:30 to 14:00 (210 to 300 minutes from 9:00), 15:30 to 17:00 (390 to 480 minutes from 9:00)
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 30, start_time >= 60)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 90, start_time >= 150)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 210, start_time >= 300)))
solver.add(Or(day != 0, Or(start_time + meeting_duration <= 390, start_time >= 480)))

# Tuesday: 9:30 to 13:00 (30 to 240 minutes from 9:00), 13:30 to 14:00 (270 to 300 minutes from 9:00),
#          14:30 to 17:00 (330 to 480 minutes from 9:00)
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 30, start_time >= 240)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 270, start_time >= 300)))
solver.add(Or(day != 1, Or(start_time + meeting_duration <= 330, start_time >= 480)))

# Wednesday: 9:00 to 9:30 (0 to 30 minutes from 9:00), 10:30 to 11:00 (90 to 120 minutes from 9:00),
#            13:30 to 14:30 (270 to 300 minutes from 9:00), 15:00 to 15:30 (360 to 390 minutes from 9:00),
#            16:00 to 16:30 (420 to 450 minutes from 9:00)
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 0, start_time >= 30)))
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 90, start_time >= 120)))
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 270, start_time >= 300)))
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 360, start_time >= 390)))
solver.add(Or(day != 2, Or(start_time + meeting_duration <= 420, start_time >= 450)))

# Judith's preference: avoid Monday, prefer Wednesday after 12:00
solver.add(day != 0)
solver.add(Or(day != 2, start_time >= 180))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{9 + start_time_value // 60}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")