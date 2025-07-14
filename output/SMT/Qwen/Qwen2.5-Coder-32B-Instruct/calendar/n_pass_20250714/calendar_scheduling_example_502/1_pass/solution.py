from z3 import *

# Define the variables for the start time of the meeting
start_time = Int('start_time')

# Constants for the meeting duration and work hours
meeting_duration = 30  # in minutes
work_start = 9 * 60    # 9:00 AM in minutes from midnight
work_end = 17 * 60     # 5:00 PM in minutes from midnight

# Jack's busy times in minutes from midnight
jack_busy_times = [
    (9 * 60 + 30, 10 * 60 + 30),  # 9:30 AM - 10:30 AM
    (11 * 60, 11 * 60 + 30),        # 11:00 AM - 11:30 AM
    (12 * 60 + 30, 13 * 60),        # 12:30 PM - 1:00 PM
    (14 * 60, 14 * 60 + 30),        # 2:00 PM - 2:30 PM
    (16 * 60, 16 * 60 + 30)         # 4:00 PM - 4:30 PM
]

# Charlotte's busy times in minutes from midnight
charlotte_busy_times = [
    (9 * 60 + 30, 10 * 60),         # 9:30 AM - 10:00 AM
    (10 * 60 + 30, 12 * 60),        # 10:30 AM - 12:00 PM
    (12 * 60 + 30, 13 * 60 + 30),   # 12:30 PM - 1:30 PM
    (14 * 60, 16 * 60)              # 2:00 PM - 4:00 PM
]

# Create a solver instance
solver = Solver()

# Add constraints for the meeting to be within work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Add constraints for Jack's availability
for busy_start, busy_end in jack_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add constraints for Charlotte's availability
for busy_start, busy_end in charlotte_busy_times:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add Jack's preference to avoid meetings after 12:30 PM
solver.add(start_time + meeting_duration <= 12 * 60 + 30)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_minutes = model[start_time].as_long()
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_minutes = start_minutes + meeting_duration
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")