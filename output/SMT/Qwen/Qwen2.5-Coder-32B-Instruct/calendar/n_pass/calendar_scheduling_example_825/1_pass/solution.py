from z3 import *

# Define the variables for the meeting day and time
day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
start_time = Int('start_time')  # in minutes since 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Day constraints
solver.add(day >= 0)
solver.add(day <= 3)

# Start time constraints (9:00 to 17:00 - 60 minutes)
solver.add(start_time >= 0)
solver.add(start_time <= 480)  # 480 minutes is 17:00 - 9:00

# Philip cannot meet on Wednesday
solver.add(day != 2)

# Laura's busy times
laura_busy_times = [
    (30, 60),   # Monday: 10:30 to 11:00
    (150, 180), # Monday: 12:30 to 13:00
    (270, 300), # Monday: 14:30 to 15:30
    (360, 480), # Monday: 16:00 to 17:00
    (30, 60),   # Tuesday: 9:30 to 10:00
    (60, 78),   # Tuesday: 11:00 to 11:30
    (180, 204), # Tuesday: 13:00 to 13:30
    (270, 300), # Tuesday: 14:30 to 15:00
    (360, 480), # Tuesday: 16:00 to 17:00
    (69, 99),   # Wednesday: 11:30 to 12:00
    (150, 180), # Wednesday: 12:30 to 13:00
    (330, 390), # Wednesday: 15:30 to 16:30
    (30, 60),   # Thursday: 10:30 to 11:00
    (120, 210), # Thursday: 12:00 to 13:30
    (240, 270), # Thursday: 15:00 to 15:30
    (360, 390)  # Thursday: 16:00 to 16:30
]

# Philip's busy times
philip_busy_times = [
    (0, 480),   # Monday: 9:00 to 17:00
    (0, 60),    # Tuesday: 9:00 to 10:00
    (60, 78),   # Tuesday: 11:00 to 11:30
    (180, 204), # Tuesday: 13:00 to 13:30
    (240, 270), # Tuesday: 14:00 to 14:30
    (300, 390), # Tuesday: 15:00 to 16:30
    (0, 60),    # Wednesday: 9:00 to 10:00
    (60, 120),  # Wednesday: 11:00 to 12:00
    (180, 960), # Wednesday: 12:30 to 16:00
    (990, 480), # Wednesday: 16:30 to 17:00
    (0, 90),    # Thursday: 9:00 to 10:30
    (60, 150),  # Thursday: 11:00 to 12:30
    (180, 480)  # Thursday: 13:00 to 17:00
]

# Add constraints for Laura's busy times
for busy_start, busy_end in laura_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add constraints for Philip's busy times
for busy_start, busy_end in philip_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration
    
    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    day_str = days[day_value]
    
    # Convert time from minutes to HH:MM format
    start_time_str = f"{start_time_value // 60 + 9:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60 + 9:02}:{end_time_value % 60:02}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")