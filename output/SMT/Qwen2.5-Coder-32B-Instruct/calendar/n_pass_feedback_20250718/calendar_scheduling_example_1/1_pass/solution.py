from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes from 00:00
work_end = 17 * 60   # 17:00 in minutes from 00:00

# Define the constraints for each participant
# Raymond's blocked times
raymond_blocked_times = [(9 * 60, 9 * 60 + 30), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (15 * 60, 15 * 60 + 30)]

# Billy's blocked times
billy_blocked_times = [(10 * 60, 10 * 60 + 30), (12 * 60, 13 * 60), (16 * 60 + 30, 17 * 60)]

# Donald's blocked times
donald_blocked_times = [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (12 * 60, 13 * 60), (14 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)]

# Billy's preference: avoid meetings after 15:00
billy_avoid_after = 15 * 60

# Create a solver instance
solver = Solver()

# Add constraints for the meeting time
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)
solver.add(end_time == start_time + meeting_duration)

# Add constraints for Raymond's availability
for blocked_start, blocked_end in raymond_blocked_times:
    solver.add(Or(start_time >= blocked_end, end_time <= blocked_start))

# Add constraints for Billy's availability
for blocked_start, blocked_end in billy_blocked_times:
    solver.add(Or(start_time >= blocked_end, end_time <= blocked_start))
solver.add(start_time < billy_avoid_after)

# Add constraints for Donald's availability
for blocked_start, blocked_end in donald_blocked_times:
    solver.add(Or(start_time >= blocked_end, end_time <= blocked_start))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[start_time].as_long()
    end_time_minutes = model[end_time].as_long()
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")