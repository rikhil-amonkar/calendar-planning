from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the days
monday, tuesday, wednesday, thursday = 0, 1, 2, 3

# Philip can't meet on Wednesday
solver.add(day != wednesday)

# Define Laura's busy times
laura_busy_times = [
    (monday, 10 * 60 + 30, 11 * 60),
    (monday, 12 * 60 + 30, 13 * 60),
    (monday, 14 * 60 + 30, 15 * 60),
    (monday, 16 * 60, 17 * 60),
    (tuesday, 9 * 60 + 30, 10 * 60),
    (tuesday, 11 * 60, 11 * 60 + 30),
    (tuesday, 13 * 60, 13 * 60 + 30),
    (tuesday, 14 * 60 + 30, 15 * 60),
    (tuesday, 16 * 60, 17 * 60),
    (wednesday, 11 * 60 + 30, 12 * 60),
    (wednesday, 12 * 60 + 30, 13 * 60),
    (wednesday, 15 * 60 + 30, 16 * 60 + 30),
    (thursday, 10 * 60 + 30, 11 * 60),
    (thursday, 12 * 60, 13 * 60 + 30),
    (thursday, 15 * 60, 15 * 60 + 30),
    (thursday, 16 * 60, 16 * 60 + 30),
]

# Define Philip's busy times
philip_busy_times = [
    (monday, 9 * 60, 17 * 60),
    (tuesday, 9 * 60, 11 * 60),
    (tuesday, 11 * 60 + 30, 12 * 60),
    (tuesday, 13 * 60, 13 * 60 + 30),
    (tuesday, 14 * 60, 14 * 60 + 30),
    (tuesday, 15 * 60, 16 * 60 + 30),
    (wednesday, 9 * 60, 10 * 60),
    (wednesday, 11 * 60, 12 * 60),
    (wednesday, 12 * 60 + 30, 16 * 60),
    (wednesday, 16 * 60 + 30, 17 * 60),
    (thursday, 9 * 60, 10 * 60 + 30),
    (thursday, 11 * 60, 12 * 60 + 30),
    (thursday, 13 * 60, 17 * 60),
]

# Add constraints for Laura's busy times
for d, s, e in laura_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for Philip's busy times
for d, s, e in philip_busy_times:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add constraints for work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for valid days
solver.add(day >= 0)
solver.add(day <= 3)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_day_str = days[meeting_day]

    # Convert time from minutes to HH:MM format
    meeting_start_time_str = f"{meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_str = f"{meeting_end_time // 60:02}:{meeting_end_time % 60:02}"

    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_time_str}\nEnd Time: {meeting_end_time_str}")
else:
    print("No solution found")