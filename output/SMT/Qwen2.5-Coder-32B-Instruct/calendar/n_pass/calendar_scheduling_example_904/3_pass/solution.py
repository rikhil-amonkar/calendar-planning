from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Daniel's busy times
daniel_busy_times = [
    (30, 60), (60, 90), (180, 210), (270, 300), (330, 360),  # Monday
    (120, 150), (180, 210), (330, 360), (390, 480),  # Tuesday
    (0, 60), (240, 270),  # Wednesday
    (60, 90), (120, 150), (270, 300), (330, 360),  # Thursday
    (0, 30), (70, 120), (180, 210), (390, 480)  # Friday
]

# Bradley's busy times
bradley_busy_times = [
    (30, 120), (70, 120), (90, 180), (240, 300),  # Monday
    (60, 120), (90, 180), (150, 210), (330, 390),  # Tuesday
    (0, 60), (60, 180), (150, 210), (270, 480),  # Wednesday
    (0, 180), (150, 210), (270, 300), (330, 390),  # Thursday
    (0, 30), (0, 180), (180, 210), (240, 270), (330, 390)  # Friday
]

# Add constraints for work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Daniel's busy times
for busy_start, busy_end in daniel_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add constraints for Bradley's busy times
for busy_start, busy_end in bradley_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add constraints for preferences
# Daniel would rather not meet on Wednesday (2) or Thursday (3)
solver.add(day != 2)
solver.add(day != 3)

# Bradley do not want to meet on Monday (0), Tuesday (1) before 12:00 (30 minutes), or Friday (4)
solver.add(day != 0)
solver.add(Or(day != 1, start_time >= 30))
solver.add(day != 4)

# Define the days of the week
days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = days_of_week[model[day].as_long()]
    meeting_start_time = 9 + model[start_time].as_long() // 60
    meeting_start_minute = model[start_time].as_long() % 60
    meeting_end_time = meeting_start_time + meeting_duration // 60
    meeting_end_minute = meeting_start_minute + meeting_duration % 60
    if meeting_end_minute >= 60:
        meeting_end_minute -= 60
        meeting_end_time += 1

    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_time:02}:{meeting_end_minute:02}")
else:
    print("No solution found")