from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Work hours are from 9:00 to 17:00, so start_time should be between 0 and 480 (10 hours * 60 minutes)
solver.add(start_time >= 0)
solver.add(start_time <= 480)

# Meeting duration is 30 minutes
meeting_duration = 30

# Amy's busy times
amy_busy_times = [
    (2, 11*60 - 9*60, 11*60 - 9*60 + 30),  # Wednesday 11:00 to 11:30
    (2, 13*60 - 9*60 + 30, 14*60 - 9*60)   # Wednesday 13:30 to 14:00
]

# Pamela's busy times
pamela_busy_times = [
    (0, 0, 1*60 + 30),  # Monday 9:00 to 10:30
    (0, 2*60, 16*60 - 9*60 + 30),  # Monday 11:00 to 16:30
    (1, 0, 30),  # Tuesday 9:00 to 9:30
    (1, 60, 480),  # Tuesday 10:00 to 17:00
    (2, 0, 30),  # Wednesday 9:00 to 9:30
    (2, 60, 11*60 - 9*60),  # Wednesday 10:00 to 11:00
    (2, 11*60 - 9*60 + 30, 13*60 - 9*60),  # Wednesday 11:30 to 13:30
    (2, 14*60 - 9*60 + 30, 15*60 - 9*60),  # Wednesday 14:30 to 15:00
    (2, 16*60 - 9*60, 16*60 - 9*60 + 30)  # Wednesday 16:00 to 16:30
]

# Add constraints for Amy's busy times
for d, s, e in amy_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Pamela's busy times
for d, s, e in pamela_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Pamela's preferences: avoid Monday and Tuesday, and Wednesday before 16:00
solver.add(day != 0)  # Avoid Monday
solver.add(day != 1)  # Avoid Tuesday
solver.add(Or(day != 2, start_time >= 7*60))  # Wednesday after 16:00

# Ensure the meeting does not start at 14:01 and end at 14:31
solver.add(Or(start_time != 14*60 - 9*60 + 1, start_time + meeting_duration != 15*60 - 9*60 + 1))

# Ensure the meeting does not start at 14:30 and end at 15:00
solver.add(Or(start_time != 14*60 - 9*60 + 30, start_time + meeting_duration != 15*60 - 9*60))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday"]
    meeting_day_str = days[meeting_day]

    # Convert time from minutes to HH:MM format
    start_hour = 9 + meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = 9 + meeting_end_time // 60
    end_minute = meeting_end_time % 60

    print(f"SOLUTION:")
    print(f"Day: {meeting_day_str}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")