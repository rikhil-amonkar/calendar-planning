from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes

# Lisa's busy times in minutes from 00:00
lisa_busy_times = [
    (9 * 60, 9 * 60 + 30),  # 9:00 to 9:30
    (10 * 60 + 30, 11 * 60),  # 10:30 to 11:00
    (14 * 60, 16 * 60)  # 14:00 to 16:00
]

# Anthony's busy times in minutes from 00:00
anthony_busy_times = [
    (9 * 60, 9 * 60 + 30),  # 9:00 to 9:30
    (11 * 60, 11 * 60 + 30),  # 11:00 to 11:30
    (12 * 60 + 30, 13 * 60 + 30),  # 12:30 to 13:30
    (14 * 60, 15 * 60),  # 14:00 to 15:00
    (15 * 60 + 30, 16 * 60),  # 15:30 to 16:00
    (16 * 60 + 30, 17 * 60)  # 16:30 to 17:00
]

# Add constraints for the meeting to be within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)
solver.add(end_time == start_time + meeting_duration)

# Add constraints to avoid busy times
for busy_start, busy_end in lisa_busy_times:
    solver.add(Or(end_time <= busy_start, start_time >= busy_end))

for busy_start, busy_end in anthony_busy_times:
    solver.add(Or(end_time <= busy_start, start_time >= busy_end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")