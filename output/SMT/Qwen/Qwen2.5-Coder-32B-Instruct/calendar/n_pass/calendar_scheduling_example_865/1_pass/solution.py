from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday, 4 for Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Day constraints
solver.add(Or(day == 1, day == 2, day == 3, day == 4))

# Meeting duration is 60 minutes
meeting_duration = 60

# Work hours are from 9:00 to 17:00, which is 480 minutes from 0 (9:00)
solver.add(start_time >= 0)
solver.add(start_time + meeting_duration <= 480)

# Megan's schedule
megan_busy_times = [
    (1, 240, 270),  # Monday 13:00 to 13:30
    (1, 240, 330),  # Monday 14:00 to 15:30
    (2, 0, 30),     # Tuesday 9:00 to 9:30
    (2, 180, 210),  # Tuesday 12:00 to 12:30
    (2, 360, 480),  # Tuesday 16:00 to 17:00
    (3, 30, 60),    # Wednesday 9:30 to 10:00
    (3, 60, 120),   # Wednesday 10:30 to 11:30
    (3, 150, 240),  # Wednesday 12:30 to 14:00
    (3, 360, 390),  # Wednesday 16:00 to 16:30
    (4, 210, 270),  # Thursday 13:30 to 14:30
    (4, 300, 330)   # Thursday 15:00 to 15:30
]

# Daniel's schedule
daniel_busy_times = [
    (1, 60, 150),   # Monday 10:00 to 11:30
    (1, 180, 330),  # Monday 12:30 to 15:00
    (2, 0, 60),     # Tuesday 9:00 to 10:00
    (2, 60, 480),   # Tuesday 10:30 to 17:00
    (3, 0, 60),     # Wednesday 9:00 to 10:00
    (3, 60, 150),   # Wednesday 10:30 to 11:30
    (3, 120, 480),  # Wednesday 12:00 to 17:00
    (4, 0, 180),    # Thursday 9:00 to 12:00
    (4, 180, 270),  # Thursday 12:30 to 14:30
    (4, 300, 330),  # Thursday 15:00 to 15:30
    (4, 360, 480)   # Thursday 16:00 to 17:00
]

# Add constraints to avoid Megan's busy times
for d, s, e in megan_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints to avoid Daniel's busy times
for d, s, e in daniel_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    
    # Convert day number to name
    days = {1: "Monday", 2: "Tuesday", 3: "Wednesday", 4: "Thursday"}
    day_name = days[day_value]
    
    # Convert start time from minutes to HH:MM format
    start_hour = 9 + start_time_value // 60
    start_minute = start_time_value % 60
    start_time_str = f"{start_hour:02}:{start_minute:02}"
    
    # Calculate end time
    end_time_value = start_time_value + meeting_duration
    end_hour = 9 + end_time_value // 60
    end_minute = end_time_value % 60
    end_time_str = f"{end_hour:02}:{end_minute:02}"
    
    # Print the solution
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")