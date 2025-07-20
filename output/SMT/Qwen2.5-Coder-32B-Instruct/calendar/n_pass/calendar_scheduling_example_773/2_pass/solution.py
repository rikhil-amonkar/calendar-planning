from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Work hours are from 9:00 to 17:00, which is 480 to 1020 minutes from 00:00
constraints.append(start_time >= 480)
constraints.append(start_time + 60 <= 1020)  # Meeting duration is 1 hour

# Day should be within the range of 0 to 2
constraints.append(day >= 0)
constraints.append(day <= 2)

# Patrick is available all week, so no additional constraints for him

# Roy's busy times
roy_busy_times = [
    (0, 600, 750),  # Monday 10:00 to 11:30
    (0, 720, 780),  # Monday 12:00 to 13:00
    (0, 840, 870),  # Monday 14:00 to 14:30
    (0, 900, 1020), # Monday 15:00 to 17:00
    (1, 630, 750),  # Tuesday 10:30 to 11:30
    (1, 720, 870),  # Tuesday 12:00 to 14:30
    (1, 900, 930),  # Tuesday 15:00 to 15:30
    (1, 960, 1020), # Tuesday 16:00 to 17:00
    (2, 570, 750),  # Wednesday 9:30 to 11:30
    (2, 750, 840),  # Wednesday 12:30 to 14:00
    (2, 870, 930),  # Wednesday 14:30 to 15:30
    (2, 990, 1020)  # Wednesday 16:30 to 17:00
]

# Add constraints to avoid Roy's busy times
for d, start, end in roy_busy_times:
    constraints.append(Or(day != d, Or(start_time + 60 <= start, start_time >= end)))

# Define the solver
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + 60

    # Convert times to HH:MM format
    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    day_str = ["Monday", "Tuesday", "Wednesday"][meeting_day]
    start_time_str = format_time(meeting_start_time - 480)  # Convert from 9:00 base
    end_time_str = format_time(meeting_end_time - 480)    # Convert from 9:00 base

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")