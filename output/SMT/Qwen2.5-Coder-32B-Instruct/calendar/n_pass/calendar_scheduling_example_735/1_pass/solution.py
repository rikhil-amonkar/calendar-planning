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

# Add constraints for Ronald's schedule
ronald_busy_times = [
    (30, 60),  # Monday 10:30 - 11:00
    (60, 90),  # Monday 12:00 - 12:30
    (330, 360),  # Monday 15:30 - 16:00
    (0, 30),  # Tuesday 9:00 - 9:30
    (60, 90),  # Tuesday 12:00 - 12:30
    (330, 390),  # Tuesday 15:30 - 16:30
    (30, 60),  # Wednesday 9:30 - 10:30
    (60, 120),  # Wednesday 11:00 - 12:00
    (150, 180),  # Wednesday 12:30 - 13:00
    (210, 240),  # Wednesday 13:30 - 14:00
    (390, 480)  # Wednesday 16:30 - 17:00
]

# Add constraints for Amber's schedule
amber_busy_times = [
    (0, 30),  # Monday 9:00 - 9:30
    (30, 60),  # Monday 10:00 - 10:30
    (80, 120),  # Monday 11:30 - 12:00
    (120, 240),  # Monday 12:30 - 14:00
    (240, 300),  # Monday 14:30 - 15:00
    (300, 480),  # Monday 15:30 - 17:00
    (0, 30),  # Tuesday 9:00 - 9:30
    (30, 70),  # Tuesday 10:00 - 11:30
    (60, 90),  # Tuesday 12:00 - 12:30
    (150, 210),  # Tuesday 13:30 - 15:30
    (390, 480),  # Tuesday 16:30 - 17:00
    (0, 30),  # Wednesday 9:00 - 9:30
    (30, 60),  # Wednesday 10:00 - 10:30
    (60, 210),  # Wednesday 11:00 - 13:30
    (300, 330)  # Wednesday 15:00 - 15:30
]

# Constraints for days
solver.add(day >= 0)
solver.add(day <= 2)

# Constraints for start time
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Constraints for Ronald's busy times
for d, (s, e) in enumerate(ronald_busy_times):
    if d // 6 == 0:  # Monday
        solver.add(Or(day != 0, Or(start_time + meeting_duration <= s, start_time >= e)))
    elif d // 6 == 1:  # Tuesday
        solver.add(Or(day != 1, Or(start_time + meeting_duration <= s, start_time >= e)))
    elif d // 6 == 2:  # Wednesday
        solver.add(Or(day != 2, Or(start_time + meeting_duration <= s, start_time >= e)))

# Constraints for Amber's busy times
for d, (s, e) in enumerate(amber_busy_times):
    if d // 6 == 0:  # Monday
        solver.add(Or(day != 0, Or(start_time + meeting_duration <= s, start_time >= e)))
    elif d // 6 == 1:  # Tuesday
        solver.add(Or(day != 1, Or(start_time + meeting_duration <= s, start_time >= e)))
    elif d // 6 == 2:  # Wednesday
        solver.add(Or(day != 2, Or(start_time + meeting_duration <= s, start_time >= e)))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{9 + start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")