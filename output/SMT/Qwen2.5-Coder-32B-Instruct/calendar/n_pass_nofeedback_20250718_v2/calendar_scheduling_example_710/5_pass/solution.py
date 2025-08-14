from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
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
    (0, 120, 180),  # Monday 11:30 to 13:00
    (0, 390, 420),  # Monday 15:30 to 16:00
    (1, 900, 930)  # Tuesday 15:00 to 15:30
]

# Kyle's busy times
kyle_busy_times = [
    (0, 0, 480),  # Monday 9:00 to 17:00
    (1, 570, 1020),  # Tuesday 9:30 to 17:00
]

# Meeting must be on Monday or Tuesday
constraints.append(Or(day == 0, day == 1))

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
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday"]
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = 9 + meeting_end // 60
    end_minute = meeting_end % 60

    print(f"SOLUTION:")
    print(f"Day: {days[meeting_day]}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")