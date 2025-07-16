from z3 import *

# Define variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Constants for time slots
meeting_duration = 30  # 30 minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the solver
solver = Solver()

# Constraints for Nicole's availability
nicole_busy_slots = [
    (0, 9 * 60, 9 * 60 + 30),  # Monday 9:00 - 9:30
    (0, 13 * 60, 13 * 60 + 30), # Monday 13:00 - 13:30
    (0, 14 * 60 + 30, 15 * 60 + 30), # Monday 14:30 - 15:30
    (1, 9 * 60, 9 * 60 + 30),  # Tuesday 9:00 - 9:30
    (1, 11 * 60 + 30, 13 * 60 + 30), # Tuesday 11:30 - 13:30
    (1, 14 * 60 + 30, 15 * 60 + 30), # Tuesday 14:30 - 15:30
    (2, 10 * 60, 11 * 60),  # Wednesday 10:00 - 11:00
    (2, 12 * 60 + 30, 15 * 60), # Wednesday 12:30 - 15:00
    (2, 16 * 60, 17 * 60)  # Wednesday 16:00 - 17:00
]

# Constraints for Ruth's availability
ruth_busy_slots = [
    (0, 9 * 60, 17 * 60),  # Monday 9:00 - 17:00
    (1, 9 * 60, 17 * 60),  # Tuesday 9:00 - 17:00
    (2, 9 * 60, 10 * 60 + 30),  # Wednesday 9:00 - 10:30
    (2, 11 * 60, 11 * 60 + 30), # Wednesday 11:00 - 11:30
    (2, 12 * 60, 12 * 60 + 30), # Wednesday 12:00 - 12:30
    (2, 13 * 60 + 30, 15 * 60 + 30), # Wednesday 13:30 - 15:30
    (2, 16 * 60, 16 * 60 + 30)  # Wednesday 16:00 - 16:30
]

# Ruth's preference: do not meet after 13:30 on Wednesday
ruth_preference = Or(day != 2, start_time <= 13 * 60 + 30)

# Add constraints to the solver
solver.add(Or(day == 0, day == 1, day == 2))  # Only consider Monday, Tuesday, Wednesday
solver.add(start_time >= work_start)  # Meeting must start after work start
solver.add(start_time + meeting_duration <= work_end)  # Meeting must end before work end

# Add Nicole's busy slots as constraints
for d, s, e in nicole_busy_slots:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add Ruth's busy slots as constraints
for d, s, e in ruth_busy_slots:
    solver.add(Or(day != d, Or(start_time + meeting_duration <= s, start_time >= e)))

# Add Ruth's preference as a constraint
solver.add(ruth_preference)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday" if model[day].as_long() == 1 else "Wednesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")