from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Define the work hours
solver.add(day >= 0)
solver.add(day <= 3)
solver.add(start_time >= 0)
solver.add(start_time <= 480)  # 480 minutes is 8 hours (from 9:00 to 17:00)

# Define the meeting duration
meeting_duration = 60  # 1 hour

# Megan's schedule
megan_busy = Or(
    And(day == 0, start_time >= 240, start_time + meeting_duration <= 270),  # 13:00 to 13:30
    And(day == 0, start_time >= 240, start_time + meeting_duration <= 930),  # 14:00 to 15:30
    And(day == 1, start_time >= 0, start_time + meeting_duration <= 30),   # 9:00 to 9:30
    And(day == 1, start_time >= 720, start_time + meeting_duration <= 750), # 12:00 to 12:30
    And(day == 1, start_time >= 960, start_time + meeting_duration <= 1020),# 16:00 to 17:00
    And(day == 2, start_time >= 180, start_time + meeting_duration <= 210), # 9:30 to 10:00
    And(day == 2, start_time >= 300, start_time + meeting_duration <= 630), # 10:30 to 11:30, 12:30 to 14:00
    And(day == 2, start_time >= 960, start_time + meeting_duration <= 990), # 16:00 to 16:30
    And(day == 3, start_time >= 810, start_time + meeting_duration <= 870), # 13:30 to 14:30
    And(day == 3, start_time >= 900, start_time + meeting_duration <= 930)  # 15:00 to 15:30
)

# Daniel's schedule
daniel_busy = Or(
    And(day == 0, start_time >= 60, start_time + meeting_duration <= 750),  # 10:00 to 11:30, 12:30 to 15:00
    And(day == 1, start_time >= 0, start_time + meeting_duration <= 60),   # 9:00 to 10:00
    And(day == 1, start_time >= 630, start_time + meeting_duration <= 1020),# 10:30 to 17:00
    And(day == 2, start_time >= 0, start_time + meeting_duration <= 60),   # 9:00 to 10:00
    And(day == 2, start_time >= 630, start_time + meeting_duration <= 1020),# 10:30 to 17:00
    And(day == 3, start_time >= 0, start_time + meeting_duration <= 720),  # 9:00 to 12:00
    And(day == 3, start_time >= 750, start_time + meeting_duration <= 870), # 12:30 to 14:30
    And(day == 3, start_time >= 900, start_time + meeting_duration <= 930), # 15:00 to 15:30
    And(day == 3, start_time >= 960, start_time + meeting_duration <= 1020) # 16:00 to 17:00
)

# Add constraints to avoid busy times
solver.add(Not(megan_busy))
solver.add(Not(daniel_busy))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_str = days[day_value]

    # Convert start and end times to HH:MM format
    start_time_str = f"{9 + start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")