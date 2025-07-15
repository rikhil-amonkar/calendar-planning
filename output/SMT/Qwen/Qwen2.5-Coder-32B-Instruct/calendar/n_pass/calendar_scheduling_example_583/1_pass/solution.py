from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constants for the meeting duration and work hours
meeting_duration = 30  # in minutes
work_start = 9 * 60    # 9:00 AM in minutes from midnight
work_end = 17 * 60     # 5:00 PM in minutes from midnight

# Create a solver instance
solver = Solver()

# Add constraints for the meeting time
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)
solver.add(end_time == start_time + meeting_duration)

# Define the busy times for Lisa and Anthony
lisa_busy_times = [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60), (14 * 60, 16 * 60)]
anthony_busy_times = [(9 * 60, 9 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60 + 30),
                      (14 * 60, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]

# Add constraints to avoid busy times for Lisa
for busy_start, busy_end in lisa_busy_times:
    solver.add(Or(start_time >= busy_end, end_time <= busy_start))

# Add constraints to avoid busy times for Anthony
for busy_start, busy_end in anthony_busy_times:
    solver.add(Or(start_time >= busy_end, end_time <= busy_start))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday"  # Since the problem specifies Monday
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = model[end_time].as_long()
    
    # Convert the meeting time from minutes to HH:MM format
    start_hour = meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = meeting_end_time // 60
    end_minute = meeting_end_time % 60
    
    print("SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")