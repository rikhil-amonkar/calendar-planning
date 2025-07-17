from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes

# Define the constraints for each participant
# Convert all times to minutes since the start of the day (00:00)

# Raymond's blocked times
raymond_blocked_times = [
    (9 * 60, 9 * 60 + 30),  # 9:00 to 9:30
    (11 * 60 + 30, 12 * 60),  # 11:30 to 12:00
    (13 * 60, 13 * 60 + 30),  # 13:00 to 13:30
    (15 * 60, 15 * 60 + 30)   # 15:00 to 15:30
]

# Billy's blocked times
billy_blocked_times = [
    (10 * 60, 10 * 60 + 30),  # 10:00 to 10:30
    (12 * 60, 13 * 60),       # 12:00 to 13:00
    (16 * 60 + 30, 17 * 60)   # 16:30 to 17:00
]

# Donald's blocked times
donald_blocked_times = [
    (9 * 60, 9 * 60 + 30),  # 9:00 to 9:30
    (10 * 60, 11 * 60),     # 10:00 to 11:00
    (12 * 60, 13 * 60),     # 12:00 to 13:00
    (14 * 60, 14 * 60 + 30),# 14:00 to 14:30
    (16 * 60, 17 * 60)      # 16:00 to 17:00
]

# Billy's preference: avoid meetings after 15:00
billy_avoid_after = 15 * 60  # 15:00 in minutes

# Create the solver
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
    
    # Convert minutes back to HH:MM format
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")