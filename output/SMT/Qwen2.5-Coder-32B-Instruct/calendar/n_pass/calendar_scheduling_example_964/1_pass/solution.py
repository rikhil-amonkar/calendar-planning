from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday, 4 for Thursday, 5 for Friday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
constraints = []

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Betty's busy times
betty_busy_times = [
    (1, 10 * 60, 10 * 60 + 30),  # Monday 10:00 to 10:30
    (1, 11 * 60 + 30, 12 * 60 + 30),  # Monday 11:30 to 12:30
    (1, 16 * 60, 16 * 60 + 30),  # Monday 16:00 to 16:30
    (2, 9 * 60 + 30, 10 * 60),  # Tuesday 9:30 to 10:00
    (2, 10 * 60 + 30, 11 * 60),  # Tuesday 10:30 to 11:00
    (2, 12 * 60, 12 * 60 + 30),  # Tuesday 12:00 to 12:30
    (2, 13 * 60 + 30, 15 * 60),  # Tuesday 13:30 to 15:00
    (2, 16 * 60 + 30, 17 * 60),  # Tuesday 16:30 to 17:00
    (3, 13 * 60 + 30, 14 * 60),  # Wednesday 13:30 to 14:00
    (3, 14 * 60 + 30, 15 * 60),  # Wednesday 14:30 to 15:00
    (5, 9 * 60, 10 * 60),  # Friday 9:00 to 10:00
    (5, 11 * 60 + 30, 12 * 60),  # Friday 11:30 to 12:00
    (5, 12 * 60 + 30, 13 * 60),  # Friday 12:30 to 13:00
    (5, 14 * 60 + 30, 15 * 60),  # Friday 14:30 to 15:00
]

# Megan's busy times
megan_busy_times = [
    (1, 9 * 60, 17 * 60),  # Monday 9:00 to 17:00
    (2, 9 * 60, 9 * 60 + 30),  # Tuesday 9:00 to 9:30
    (2, 10 * 60, 10 * 60 + 30),  # Tuesday 10:00 to 10:30
    (2, 12 * 60, 14 * 60),  # Tuesday 12:00 to 14:00
    (2, 15 * 60, 15 * 60 + 30),  # Tuesday 15:00 to 15:30
    (2, 16 * 60, 16 * 60 + 30),  # Tuesday 16:00 to 16:30
    (3, 9 * 60 + 30, 10 * 60 + 30),  # Wednesday 9:30 to 10:30
    (3, 11 * 60, 11 * 60 + 30),  # Wednesday 11:00 to 11:30
    (3, 12 * 60 + 30, 13 * 60),  # Wednesday 12:30 to 13:00
    (3, 13 * 60 + 30, 14 * 60 + 30),  # Wednesday 13:30 to 14:30
    (3, 15 * 60 + 30, 17 * 60),  # Wednesday 15:30 to 17:00
    (4, 9 * 60, 10 * 60 + 30),  # Thursday 9:00 to 10:30
    (4, 11 * 60 + 30, 14 * 60),  # Thursday 11:30 to 14:00
    (4, 14 * 60 + 30, 15 * 60),  # Thursday 14:30 to 15:00
    (4, 15 * 60 + 30, 16 * 60 + 30),  # Thursday 15:30 to 16:30
    (5, 9 * 60, 17 * 60),  # Friday 9:00 to 17:00
]

# Constraints for the day
constraints.append(Or(day == 1, day == 2, day == 5))  # Betty can't meet on Wednesday or Thursday

# Constraints for the time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Constraints for Betty's busy times
for d, s, e in betty_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Constraints for Megan's busy times
for d, s, e in megan_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Solve the problem
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    meeting_day_str = days[meeting_day - 1]

    # Convert time from minutes to HH:MM format
    meeting_start_time_str = f"{meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_str = f"{meeting_end_time // 60:02}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_time_str}\nEnd Time: {meeting_end_time_str}")
else:
    print("No solution found")