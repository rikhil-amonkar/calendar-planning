from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define work hours in minutes from midnight
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM

# Define existing busy schedules for Judy and Nicole in minutes
nicole_busy = [
    (9 * 60, 10 * 60),      # 9:00 to 10:00
    (10 * 60 + 30, 16 * 60) # 10:30 to 4:30 PM
]

# Define variables for meeting start and end times (in minutes)
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 30  # in minutes

# Constraints to ensure the meeting duration is half an hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Ensure the meeting does not overlap with Nicole's busy schedule
for busy_start, busy_end in nicole_busy:
    solver.add(Or(start_time < busy_start, end_time > busy_end))

# Additional constraint: Nicole prefers not to meet before 16:00
solver.add(start_time >= (16 * 60))  # 16:00 in minutes

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    start = model[start_time].as_long()
    end = model[end_time].as_long()
    
    # Convert back to standard time for output
    start_hour = start // 60
    start_minute = start % 60
    end_hour = end // 60
    end_minute = end % 60
    
    print(f"SOLUTION: Meeting on Monday from {start_hour:02}:{start_minute:02} to {end_hour:02}:{end_minute:02}")
else:
    print("No available time slot found.")