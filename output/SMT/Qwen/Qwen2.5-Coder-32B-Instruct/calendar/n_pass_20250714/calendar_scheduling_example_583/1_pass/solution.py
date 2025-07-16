from z3 import *

# Define the variables
day = "Monday"
start_time = Int('start_time')
end_time = Int('end_time')
meeting_duration = 30  # in minutes

# Define the working hours
work_start = 9 * 60  # 9:00 in minutes from 00:00
work_end = 17 * 60   # 17:00 in minutes from 00:00

# Define the busy times for Lisa and Anthony
lisa_busy_times = [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (14*60, 16*60)]
anthony_busy_times = [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (12*60 + 30, 13*60 + 30),
                      (14*60, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]

# Create a solver instance
solver = Solver()

# Add constraints for the meeting time
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
    start_minutes = model[start_time].as_long()
    end_minutes = model[end_time].as_long()
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")