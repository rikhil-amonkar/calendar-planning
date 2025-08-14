from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Define the meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Define the days
days = 3  # Monday, Tuesday, Wednesday

# Nicole's busy times
nicole_busy_times = [
    (0, 0, 30),  # Monday 9:00 - 9:30
    (0, 240, 270),  # Monday 13:00 - 13:30
    (0, 330, 360),  # Monday 14:30 - 15:30
    (1, 0, 30),  # Tuesday 9:00 - 9:30
    (1, 150, 300),  # Tuesday 11:30 - 13:30
    (1, 330, 360),  # Tuesday 14:30 - 15:30
    (2, 60, 120),  # Wednesday 10:00 - 11:00
    (2, 210, 360),  # Wednesday 12:30 - 15:00
    (2, 420, 480)  # Wednesday 16:00 - 17:00
]

# Ruth's busy times
ruth_busy_times = [
    (0, 0, 480),  # Monday 9:00 - 17:00
    (1, 0, 480),  # Tuesday 9:00 - 17:00
    (2, 0, 60),  # Wednesday 9:00 - 10:30
    (2, 60, 90),  # Wednesday 11:00 - 11:30
    (2, 120, 150),  # Wednesday 12:00 - 12:30
    (2, 210, 300),  # Wednesday 13:30 - 15:30
    (2, 390, 420)  # Wednesday 16:00 - 16:30
]

# Ruth's preference: do not meet on Wednesday after 13:30
ruth_preference = (2, 210, 480)

# Add constraints for days
constraints.append(day >= 0)
constraints.append(day < days)

# Add constraints for start time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Add constraints for Nicole's busy times
for d, s, e in nicole_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Ruth's busy times
for d, s, e in ruth_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add Ruth's preference
constraints.append(Or(day != 2, start_time + meeting_duration <= 210))

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
    day_str = ["Monday", "Tuesday", "Wednesday"][day_value]

    # Convert time from minutes to HH:MM format
    start_time_str = f"{9 + start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60:02}:{end_time_value % 60:02}"

    # Print the solution
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")