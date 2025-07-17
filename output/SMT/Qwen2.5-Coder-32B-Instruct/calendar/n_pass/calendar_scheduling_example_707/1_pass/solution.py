from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Ryan's schedule
ryan_busy = [
    (0, 9 * 60 + 30, 10 * 60),  # Monday 9:30 - 10:00
    (0, 11 * 60, 12 * 60),      # Monday 11:00 - 12:00
    (0, 13 * 60, 13 * 60 + 30), # Monday 13:00 - 13:30
    (0, 15 * 60 + 30, 16 * 60), # Monday 15:30 - 16:00
    (1, 11 * 60 + 30, 12 * 60 + 30), # Tuesday 11:30 - 12:30
    (1, 15 * 60 + 30, 16 * 60), # Tuesday 15:30 - 16:00
    (2, 12 * 60, 13 * 60),      # Wednesday 12:00 - 13:00
    (2, 15 * 60 + 30, 16 * 60), # Wednesday 15:30 - 16:00
    (2, 16 * 60 + 30, 17 * 60)  # Wednesday 16:30 - 17:00
]

# Adam's schedule
adam_busy = [
    (0, 9 * 60, 10 * 60 + 30),  # Monday 9:00 - 10:30
    (0, 11 * 60, 13 * 60 + 30), # Monday 11:00 - 13:30
    (0, 14 * 60, 16 * 60),      # Monday 14:00 - 16:00
    (0, 16 * 60 + 30, 17 * 60), # Monday 16:30 - 17:00
    (1, 9 * 60, 10 * 60),       # Tuesday 9:00 - 10:00
    (1, 10 * 60 + 30, 15 * 60 + 30), # Tuesday 10:30 - 15:30
    (1, 16 * 60, 17 * 60),      # Tuesday 16:00 - 17:00
    (2, 9 * 60, 9 * 60 + 30),   # Wednesday 9:00 - 9:30
    (2, 10 * 60, 11 * 60),      # Wednesday 10:00 - 11:00
    (2, 11 * 60 + 30, 14 * 60 + 30), # Wednesday 11:30 - 14:30
    (2, 15 * 60, 15 * 60 + 30), # Wednesday 15:00 - 15:30
    (2, 16 * 60, 16 * 60 + 30)  # Wednesday 16:00 - 16:30
]

# Constraints for the day
solver.add(day >= 0)
solver.add(day <= 2)

# Constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Ryan's availability
for d, s, e in ryan_busy:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Adam's availability
for d, s, e in adam_busy:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Adam's preference to avoid meetings on Monday before 14:30
solver.add(Or(day != 0, start_time >= 14 * 60))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday"]
    meeting_day_str = days[meeting_day]

    # Convert time from minutes to HH:MM format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60

    print(f"SOLUTION:")
    print(f"Day: {meeting_day_str}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")