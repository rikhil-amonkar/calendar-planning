from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constants for the meeting duration and work hours
meeting_duration = 30  # 30 minutes
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60  # 5:00 PM

# Define the constraints for Robert's schedule
robert_busy_times = [
    (11 * 60, 11 * 60 + 30),  # Monday 11:00 - 11:30
    (14 * 60, 14 * 60 + 30),  # Monday 14:00 - 14:30
    (15 * 60 + 30, 16 * 60),  # Monday 15:30 - 16:00
    (10 * 60 + 30, 11 * 60),  # Tuesday 10:30 - 11:00
    (15 * 60, 15 * 60 + 30),  # Tuesday 15:00 - 15:30
    (10 * 60, 11 * 60),       # Wednesday 10:00 - 11:00
    (11 * 60 + 30, 12 * 60),  # Wednesday 11:30 - 12:00
    (12 * 60 + 30, 13 * 60),  # Wednesday 12:30 - 13:00
    (13 * 60 + 30, 14 * 60),  # Wednesday 13:30 - 14:00
    (15 * 60, 15 * 60 + 30),  # Wednesday 15:00 - 15:30
    (16 * 60, 16 * 60 + 30)   # Wednesday 16:00 - 16:30
]

# Define the constraints for Ralph's schedule
ralph_busy_times = [
    (10 * 60, 13 * 60 + 30),  # Monday 10:00 - 13:30
    (14 * 60, 14 * 60 + 30),  # Monday 14:00 - 14:30
    (15 * 60, 17 * 60),       # Monday 15:00 - 17:00
    (9 * 60, 9 * 60 + 30),    # Tuesday 9:00 - 9:30
    (10 * 60, 10 * 60 + 30),  # Tuesday 10:00 - 10:30
    (11 * 60, 11 * 60 + 30),  # Tuesday 11:00 - 11:30
    (12 * 60, 13 * 60),       # Tuesday 12:00 - 13:00
    (14 * 60, 15 * 60 + 30),  # Tuesday 14:00 - 15:30
    (16 * 60, 17 * 60),       # Tuesday 16:00 - 17:00
    (10 * 60 + 30, 11 * 60),  # Wednesday 10:30 - 11:00
    (11 * 60 + 30, 12 * 60),  # Wednesday 11:30 - 12:00
    (13 * 60, 14 * 60 + 30),  # Wednesday 13:00 - 14:30
    (16 * 60 + 30, 17 * 60)   # Wednesday 16:30 - 17:00
]

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(Or(day == 0, day == 1, day == 2))

# Add constraints for the start time within work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints to avoid Robert's busy times
for busy_start, busy_end in robert_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add constraints to avoid Ralph's busy times
for busy_start, busy_end in ralph_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Robert prefers not to have more meetings on Monday, so we add a soft constraint
# We do this by minimizing the day variable, which will prioritize earlier days
objective = Optimize()
objective.add(solver.assertions())
objective.minimize(day)

# Check if the solution exists
if objective.check() == sat:
    model = objective.model()
    meeting_day = "Monday" if model[day] == 0 else "Tuesday" if model[day] == 1 else "Wednesday"
    meeting_start = model[start_time].as_long()
    meeting_start_hour = meeting_start // 60
    meeting_start_minute = meeting_start % 60
    meeting_end = meeting_start + meeting_duration
    meeting_end_hour = meeting_end // 60
    meeting_end_minute = meeting_end % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")