from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the meeting duration
meeting_duration = 60  # 1 hour

# Define the days
days = 5  # Monday to Friday

# Nicole's busy times
nicole_busy_times = [
    (1, 16 * 60, 16 * 60 + 30),  # Tuesday 16:00 to 16:30
    (2, 15 * 60, 15 * 60 + 30),  # Wednesday 15:00 to 15:30
    (4, 12 * 60, 12 * 60 + 30),  # Friday 12:00 to 12:30
    (4, 15 * 60 + 30, 16 * 60)   # Friday 15:30 to 16:00
]

# Daniel's busy times
daniel_busy_times = [
    (0, 9 * 60, 12 * 60 + 30),  # Monday 9:00 to 12:30
    (0, 13 * 60, 13 * 60 + 30), # Monday 13:00 to 13:30
    (0, 14 * 60, 16 * 60 + 30), # Monday 14:00 to 16:30
    (1, 9 * 60, 10 * 60 + 30),  # Tuesday 9:00 to 10:30
    (1, 11 * 60 + 30, 12 * 60 + 30), # Tuesday 11:30 to 12:30
    (1, 13 * 60, 13 * 60 + 30), # Tuesday 13:00 to 13:30
    (1, 15 * 60, 16 * 60),      # Tuesday 15:00 to 16:00
    (1, 16 * 60 + 30, 17 * 60), # Tuesday 16:30 to 17:00
    (2, 9 * 60, 10 * 60),       # Wednesday 9:00 to 10:00
    (2, 11 * 60, 12 * 60 + 30), # Wednesday 11:00 to 12:30
    (2, 13 * 60, 13 * 60 + 30), # Wednesday 13:00 to 13:30
    (2, 14 * 60, 14 * 60 + 30), # Wednesday 14:00 to 14:30
    (2, 16 * 60 + 30, 17 * 60), # Wednesday 16:30 to 17:00
    (3, 11 * 60, 12 * 60),       # Thursday 11:00 to 12:00
    (3, 13 * 60, 14 * 60),       # Thursday 13:00 to 14:00
    (3, 15 * 60, 15 * 60 + 30), # Thursday 15:00 to 15:30
    (4, 10 * 60, 11 * 60),       # Friday 10:00 to 11:00
    (4, 11 * 60 + 30, 12 * 60), # Friday 11:30 to 12:00
    (4, 12 * 60 + 30, 14 * 60 + 30), # Friday 12:30 to 14:30
    (4, 15 * 60, 15 * 60 + 30), # Friday 15:00 to 15:30
    (4, 16 * 60, 16 * 60 + 30)  # Friday 16:00 to 16:30
]

# Constraints for the day and start time
constraints.append(day >= 0)
constraints.append(day < days)
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Constraints for Nicole's availability
for d, s, e in nicole_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Constraints for Daniel's availability
for d, s, e in daniel_busy_times:
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert the day number to a string
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    meeting_day_str = days_of_week[meeting_day]

    # Convert the start and end times to HH:MM format
    meeting_start_time_str = f"{meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_str = f"{meeting_end_time // 60:02}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_time_str}\nEnd Time: {meeting_end_time_str}")
else:
    print("No solution found")