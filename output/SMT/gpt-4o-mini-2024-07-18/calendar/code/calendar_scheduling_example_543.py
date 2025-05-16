from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define work hours
work_start = 9 * 60  # Convert to minutes (9:00 AM)
work_end = 17 * 60   # Convert to minutes (5:00 PM)

# Define existing busy schedules for James and John in minutes
james_busy = [(11 * 60 + 30, 12 * 60), (14 * 60 + 30, 15 * 60)]
john_busy = [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), 
             (12 * 60 + 30, 13 * 60), (14 * 60 + 30, 16 * 60)]

# Define variables for meeting start and end times (in minutes)
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 60  # in minutes

# Constraints to ensure total meeting time is one hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Ensure the meeting does not overlap with James's busy schedule
for busy_start, busy_end in james_busy:
    solver.add(Or(start_time < busy_start, end_time > busy_end))

# Ensure the meeting does not overlap with John's busy schedule
for busy_start, busy_end in john_busy:
    solver.add(Or(start_time < busy_start, end_time > busy_end))

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