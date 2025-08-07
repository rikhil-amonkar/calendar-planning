from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Define the work hours in minutes from 9:00
work_start = 0  # 9:00
work_end = 480  # 17:00

# Define the meeting duration in minutes
meeting_duration = 60

# Define the busy times for Roy
roy_busy_times = [
    (60, 90),  # Monday 10:00 to 11:30
    (120, 150),  # Monday 12:00 to 13:00
    (240, 270),  # Monday 14:00 to 14:30
    (300, 480),  # Monday 15:00 to 17:00
    (630, 750),  # Tuesday 10:30 to 11:30
    (720, 870),  # Tuesday 12:00 to 14:30
    (930, 990),  # Tuesday 15:00 to 15:30
    (960, 1020),  # Tuesday 16:00 to 17:00
    (1230, 1350),  # Wednesday 9:30 to 11:30
    (1350, 1470),  # Wednesday 12:30 to 14:00
    (1650, 1710),  # Wednesday 14:30 to 15:30
    (1710, 1830)  # Wednesday 16:30 to 17:00
]

# Add constraints for the day
constraints.append(day >= 0)
constraints.append(day <= 2)

# Add constraints for the start time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Add constraints for Roy's busy times
for d in range(3):
    for busy_start, busy_end in roy_busy_times:
        # Convert busy times to the correct day
        busy_start += d * 1440  # 1440 minutes in a day
        busy_end += d * 1440
        # Add constraints to avoid busy times
        constraints.append(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert the day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
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