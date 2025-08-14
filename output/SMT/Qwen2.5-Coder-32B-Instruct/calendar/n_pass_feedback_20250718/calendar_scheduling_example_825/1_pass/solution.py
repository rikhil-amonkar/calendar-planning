from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Define the days
days = 4  # Monday to Thursday

# Define the constraints for each person
# Laura's busy times
laura_busy_times = [
    (30, 60),  # Monday 10:30 - 11:00
    (150, 180),  # Monday 12:30 - 13:00
    (270, 300),  # Monday 14:30 - 15:30
    (360, 480),  # Monday 16:00 - 17:00
    (0, 30),  # Tuesday 9:30 - 10:00
    (60, 78),  # Tuesday 11:00 - 11:30
    (180, 210),  # Tuesday 13:00 - 13:30
    (270, 300),  # Tuesday 14:30 - 15:00
    (360, 480),  # Tuesday 16:00 - 17:00
    (90, 120),  # Wednesday 11:30 - 12:00
    (150, 180),  # Wednesday 12:30 - 13:00
    (330, 450),  # Wednesday 15:30 - 16:30
    (30, 60),  # Thursday 10:30 - 11:00
    (120, 210),  # Thursday 12:00 - 13:30
    (240, 270),  # Thursday 15:00 - 15:30
    (360, 390)  # Thursday 16:00 - 16:30
]

# Philip's busy times
philip_busy_times = [
    (0, 480),  # Monday 9:00 - 17:00
    (0, 60),  # Tuesday 9:00 - 10:00
    (60, 78),  # Tuesday 11:00 - 11:30
    (180, 210),  # Tuesday 13:00 - 13:30
    (240, 270),  # Tuesday 14:00 - 14:30
    (300, 390),  # Tuesday 15:00 - 16:30
    (0, 60),  # Wednesday 9:00 - 10:00
    (60, 78),  # Wednesday 11:00 - 12:00
    (180, 990),  # Wednesday 12:30 - 16:00
    (990, 990),  # Wednesday 16:30 - 17:00 (This is a dummy value to keep the format)
    (0, 60),  # Thursday 9:00 - 10:30
    (60, 150),  # Thursday 11:00 - 12:30
    (180, 990)  # Thursday 13:00 - 17:00 (This is a dummy value to keep the format)
]

# Philip cannot meet on Wednesday
solver.add(day != 2)

# Define the constraints for the meeting time
solver.add(day >= 0)
solver.add(day < days)
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Laura's busy times
for busy_start, busy_end in laura_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add constraints for Philip's busy times
for busy_start, busy_end in philip_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert meeting day to string
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_day_str = days_of_week[meeting_day]

    # Convert meeting start and end times to HH:MM format
    meeting_start_str = f"{9 + meeting_start // 60:02}:{meeting_start % 60:02}"
    meeting_end_str = f"{9 + meeting_end // 60:02}:{meeting_end % 60:02}"

    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_str}\nEnd Time: {meeting_end_str}")
else:
    print("No solution found")