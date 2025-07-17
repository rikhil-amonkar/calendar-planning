from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# Meeting should be between 9:00 and 17:00 on Monday
solver.add(day == 1)  # Monday is represented by 1
solver.add(start_time >= 9 * 60)  # 9:00 in minutes
solver.add(end_time <= 17 * 60)  # 17:00 in minutes
solver.add(end_time == start_time + meeting_duration)

# Eric's blocked times
eric_blocked_times = [(12 * 60, 13 * 60), (14 * 60, 15 * 60)]
for start, end in eric_blocked_times:
    solver.add(Or(end_time <= start, start_time >= end))

# Henry's blocked times
henry_blocked_times = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30),
                       (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]
for start, end in henry_blocked_times:
    solver.add(Or(end_time <= start, start_time >= end))

# Henry prefers not to meet after 10:00
solver.add(start_time < 10 * 60)

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