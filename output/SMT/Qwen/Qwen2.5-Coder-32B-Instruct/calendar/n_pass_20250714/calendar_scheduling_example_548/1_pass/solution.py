from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
meeting_duration = 30

# The meeting should be between 9:00 and 17:00 on Monday
solver.add(day == 1)  # Monday is represented as 1
solver.add(start_time >= 9 * 60)  # 9:00 in minutes
solver.add(end_time <= 17 * 60)  # 17:00 in minutes
solver.add(end_time - start_time == meeting_duration)

# Judy is free the entire day, so no additional constraints for her

# Nicole's busy times are from 9:00 to 10:00 and from 10:30 to 16:30
# Convert these times to minutes
nicole_busy_times = [(9 * 60, 10 * 60), (10 * 60 + 30, 16 * 60 + 30)]

# Add constraints to avoid Nicole's busy times
for busy_start, busy_end in nicole_busy_times:
    solver.add(Or(end_time <= busy_start, start_time >= busy_end))

# Nicole prefers not to meet before 16:00
solver.add(start_time >= 16 * 60)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = model[end_time].as_long()
    
    # Convert the meeting time back to HH:MM format
    start_hour = meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = meeting_end_time // 60
    end_minute = meeting_end_time % 60
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")