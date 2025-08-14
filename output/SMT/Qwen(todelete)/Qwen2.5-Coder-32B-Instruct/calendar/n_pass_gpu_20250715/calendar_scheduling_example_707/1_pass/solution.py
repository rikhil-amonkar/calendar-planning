from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = 540  # 9:00 in minutes
work_end = 1020   # 17:00 in minutes

# Ryan's busy times
ryan_busy_times = [
    (1, 570, 600),  # Monday 9:30 to 10:00
    (1, 660, 720),  # Monday 11:00 to 12:00
    (1, 810, 810 + 30),  # Monday 13:30 to 13:30 + 30
    (1, 930, 990),  # Monday 15:30 to 16:00
    (2, 690, 750),  # Tuesday 11:30 to 12:30
    (2, 930, 990),  # Tuesday 15:30 to 16:00
    (3, 720, 780),  # Wednesday 12:00 to 13:00
    (3, 930, 990),  # Wednesday 15:30 to 16:00
    (3, 990, 1020)  # Wednesday 16:30 to 17:00
]

# Adam's busy times
adam_busy_times = [
    (1, 540, 630),  # Monday 9:00 to 10:30
    (1, 660, 810),  # Monday 11:00 to 13:30
    (1, 840, 960),  # Monday 14:00 to 16:00
    (1, 990, 1020),  # Monday 16:30 to 17:00
    (2, 540, 600),  # Tuesday 9:00 to 10:00
    (2, 630, 930),  # Tuesday 10:30 to 15:30
    (2, 960, 1020),  # Tuesday 16:00 to 17:00
    (3, 540, 570),  # Wednesday 9:00 to 9:30
    (3, 600, 660),  # Wednesday 10:00 to 11:00
    (3, 690, 870),  # Wednesday 11:30 to 14:30
    (3, 900, 930),  # Wednesday 15:00 to 15:30
    (3, 960, 990)   # Wednesday 16:00 to 16:30
]

# Ryan cannot meet on Wednesday
constraints.append(day != 3)

# Adam prefers not to have meetings on Monday before 14:30 (870 minutes)
constraints.append(Or(day != 1, start_time >= 870))

# Day should be between 1 (Monday) and 3 (Wednesday)
constraints.append(And(day >= 1, day <= 3))

# Start time should be within work hours and allow for a 30-minute meeting
constraints.append(And(start_time >= work_start, start_time + meeting_duration <= work_end))

# Add constraints to avoid busy times
for d, s, e in ryan_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

for d, s, e in adam_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration
    
    # Convert day number to string
    day_str = {1: "Monday", 2: "Tuesday", 3: "Wednesday"}[day_value]
    
    # Convert start and end times to HH:MM format
    start_time_str = f"{(start_time_value // 60):02}:{(start_time_value % 60):02}"
    end_time_str = f"{(end_time_value // 60):02}:{(end_time_value % 60):02}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")