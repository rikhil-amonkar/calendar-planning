from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0  # 9:00
work_end = 480  # 17:00

# Cheryl's busy times
cheryl_busy_times = [
    (0, 0, 30),  # Monday 9:00 to 9:30
    (0, 150, 240),  # Monday 11:30 to 13:00
    (0, 390, 420),  # Monday 15:30 to 16:00
    (1, 900, 930)  # Tuesday 15:00 to 15:30
]

# Kyle's busy times
kyle_busy_times = [
    (0, 0, 480),  # Monday 9:00 to 17:00
    (1, 570, 1020),  # Tuesday 9:30 to 17:00
    (2, 0, 30),  # Wednesday 9:00 to 9:30
    (2, 60, 240),  # Wednesday 10:00 to 13:00
    (2, 810, 840),  # Wednesday 13:30 to 14:00
    (2, 870, 1020)  # Wednesday 14:30 to 17:00
]

# Cheryl can't meet on Wednesday
constraints.append(day != 2)

# Meeting must be within work hours
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Meeting must not overlap with Cheryl's busy times
for d, s, e in cheryl_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Meeting must not overlap with Kyle's busy times
for d, s, e in kyle_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert day and times to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{9 + meeting_start_time // 60}:{meeting_start_time % 60:02}"
    end_time_str = f"{9 + meeting_end_time // 60}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {days[meeting_day]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")