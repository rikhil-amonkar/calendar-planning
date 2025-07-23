from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Define the blocked times for Ronald
ronald_blocked_times = [
    (30, 60),  # Monday 10:30 - 11:00
    (60, 90),  # Monday 12:00 - 12:30
    (390, 420),  # Monday 15:30 - 16:00
    (0, 30),  # Tuesday 9:00 - 9:30
    (60, 90),  # Tuesday 12:00 - 12:30
    (390, 450),  # Tuesday 15:30 - 16:30
    (30, 60),  # Wednesday 9:30 - 10:30
    (120, 150),  # Wednesday 11:00 - 12:00
    (180, 210),  # Wednesday 12:30 - 13:00
    (270, 300),  # Wednesday 13:30 - 14:00
    (450, 480)  # Wednesday 16:30 - 17:00
]

# Define the blocked times for Amber
amber_blocked_times = [
    (0, 30),  # Monday 9:00 - 9:30
    (30, 60),  # Monday 10:00 - 10:30
    (90, 120),  # Monday 11:30 - 12:00
    (120, 240),  # Monday 12:30 - 14:00
    (240, 300),  # Monday 14:30 - 15:00
    (300, 480),  # Monday 15:30 - 17:00
    (0, 30),  # Tuesday 9:00 - 9:30
    (30, 90),  # Tuesday 10:00 - 11:30
    (60, 90),  # Tuesday 12:00 - 12:30
    (180, 300),  # Tuesday 13:30 - 15:30
    (450, 480),  # Tuesday 16:30 - 17:00
    (0, 30),  # Wednesday 9:00 - 9:30
    (30, 60),  # Wednesday 10:00 - 10:30
    (60, 210),  # Wednesday 11:00 - 13:30
    (300, 330)  # Wednesday 15:00 - 15:30
]

# Constraints for the day
solver.add(day >= 0)
solver.add(day <= 2)

# Constraints for the start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Constraints for Ronald's blocked times
for blocked_start, blocked_end in ronald_blocked_times:
    solver.add(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Constraints for Amber's blocked times
for blocked_start, blocked_end in amber_blocked_times:
    solver.add(Or(start_time + meeting_duration <= blocked_start, start_time >= blocked_end))

# Add possible meeting times on Wednesday
possible_meeting_times = [
    (2, 840),  # 14:00 - 14:30
    (2, 900),  # 15:00 - 15:30
    (2, 960)   # 16:00 - 16:30
]

# Add constraints for possible meeting times
for d, t in possible_meeting_times:
    solver.add(Or(day != d, start_time != t))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{9 + start_time_value // 60}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")