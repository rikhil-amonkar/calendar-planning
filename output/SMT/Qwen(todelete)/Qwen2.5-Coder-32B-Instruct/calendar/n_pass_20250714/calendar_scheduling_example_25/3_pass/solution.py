from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
s = Solver()

# The meeting must be on Monday
s.add(day == "Monday")

# The meeting duration is one hour
s.add(end_time == start_time + 60)

# Work hours are from 9:00 to 17:00 (540 to 1020 in minutes from 00:00)
s.add(start_time >= 540)
s.add(end_time <= 1020)

# Anthony's busy times
s.add(Or(start_time >= 630, end_time <= 600))  # 9:30 to 10:00
s.add(Or(start_time >= 780, end_time <= 720))  # 12:00 to 13:00
s.add(Or(start_time >= 960, end_time <= 990))  # 16:00 to 16:30

# Pamela's busy times
s.add(Or(start_time >= 630, end_time <= 600))  # 9:30 to 10:00
s.add(Or(start_time >= 990, end_time <= 990))  # 16:30 to 17:00
s.add(end_time <= 870)  # Pamela does not want to meet after 14:30 (870 minutes from 00:00)

# Zachary's busy times
s.add(Or(start_time >= 690, end_time <= 540))  # 9:00 to 11:30
s.add(Or(start_time >= 720, end_time <= 720))  # 12:00 to 12:30
s.add(Or(start_time >= 780, end_time <= 780))  # 13:00 to 13:30
s.add(Or(start_time >= 870, end_time <= 870))  # 14:30 to 15:00
s.add(Or(start_time >= 960, end_time <= 960))  # 16:00 to 17:00

# Check if there is a solution
if s.check() == sat:
    m = s.model()
    start_hour = m[start_time].as_long() // 60
    start_minute = m[start_time].as_long() % 60
    end_hour = m[end_time].as_long() // 60
    end_minute = m[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: {m[day]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")