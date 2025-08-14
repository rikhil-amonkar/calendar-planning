from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')  # in minutes from 00:00
end_time = Int('end_time')    # in minutes from 00:00

# Constants for the problem
meeting_duration = 30  # 30 minutes
work_start = 540       # 09:00 in minutes from 00:00
work_end = 1020        # 17:00 in minutes from 00:00

# Jack's busy times in minutes from 00:00
jack_busy_times = [(570, 630), (660, 690), (750, 780), (840, 870), (960, 990)]

# Charlotte's busy times in minutes from 00:00
charlotte_busy_times = [(570, 600), (630, 720), (750, 810), (840, 960)]

# Create a solver instance
solver = Solver()

# Add constraints for the day
solver.add(day == "Monday")

# Add constraints for the time range within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)
solver.add(end_time - start_time == meeting_duration)

# Add constraints to avoid Jack's busy times
for s, e in jack_busy_times:
    solver.add(Or(end_time <= s, start_time >= e))

# Add constraints to avoid Charlotte's busy times
for s, e in charlotte_busy_times:
    solver.add(Or(end_time <= s, start_time >= e))

# Add Jack's preference to avoid meetings after 12:30
solver.add(start_time < 750)  # 12:30 in minutes from 00:00

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: {model[day]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")