from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = 540
work_end = 1020
meeting_duration = 30  # 30 minutes

# Define the days
monday, tuesday, wednesday, thursday = 0, 1, 2, 3

# Ruth's busy times in minutes from 00:00
ruth_busy_times = [
    (540, 1020),  # Monday
    (540, 1020),  # Tuesday
    (540, 1020),  # Wednesday
    (540, 690),   # Thursday 9:00 to 11:30
    (705, 860),   # Thursday 11:30 to 14:30
    (900, 1020)   # Thursday 15:00 to 17:00
]

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(day >= 0)
solver.add(day <= 3)

# Add constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Ruth's busy times
for i, (busy_start, busy_end) in enumerate(ruth_busy_times):
    if i == 3:  # Thursday
        # Julie would like to avoid more meetings on Thursday before 11:30 (690 minutes)
        solver.add(Or(day != thursday, start_time >= 690))
    solver.add(Or(day != i, start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert meeting day to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_day_str = days[meeting_day]

    # Convert meeting start and end times to HH:MM format
    meeting_start_str = f"{meeting_start // 60:02}:{meeting_start % 60:02}"
    meeting_end_str = f"{meeting_end // 60:02}:{meeting_end % 60:02}"

    # Print the solution
    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_str}\nEnd Time: {meeting_end_str}")
else:
    print("No solution found")