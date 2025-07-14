from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constants for the problem
meeting_duration = 30  # in minutes
work_start = 9 * 60    # 9:00 in minutes from 00:00
work_end = 17 * 60     # 17:00 in minutes from 00:00

# Eric's blocked times in minutes from 00:00
eric_blocked_times = [(12 * 60, 13 * 60), (14 * 60, 15 * 60)]

# Henry's blocked times in minutes from 00:00
henry_blocked_times = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60),
                       (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30),
                       (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]

# Henry prefers not to meet after 10:00
henry_preference_end_time = 10 * 60

# Create the solver
solver = Solver()

# Add constraints
solver.add(day == 1)  # We are only considering Monday
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)
solver.add(end_time == start_time + meeting_duration)

# Eric's constraints
for blocked_start, blocked_end in eric_blocked_times:
    solver.add(Or(end_time <= blocked_start, start_time >= blocked_end))

# Henry's constraints
for blocked_start, blocked_end in henry_blocked_times:
    solver.add(Or(end_time <= blocked_start, start_time >= blocked_end))

# Henry's preference
solver.add(end_time <= henry_preference_end_time)

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