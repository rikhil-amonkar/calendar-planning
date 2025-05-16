from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define work hours in minutes from midnight
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM

# Define existing busy schedules for Anthony, Pamela, and Zachary in minutes
anthony_busy = [
    (9 * 60 + 30, 10 * 60),   # 9:30 to 10:00
    (12 * 60, 13 * 60),       # 12:00 to 1:00
    (16 * 60, 16 * 60 + 30)   # 4:00 to 4:30
]

pamela_busy = [
    (9 * 60 + 30, 10 * 60),   # 9:30 to 10:00
    (16 * 60 + 30, 17 * 60)   # 4:30 to 5:00
]

zachary_busy = [
    (9 * 60, 11 * 60 + 30),   # 9:00 to 11:30
    (12 * 60, 12 * 60 + 30),  # 12:00 to 12:30
    (13 * 60, 13 * 60 + 30),  # 1:00 to 1:30
    (14 * 60 + 30, 15 * 60),   # 2:30 to 3:00
    (16 * 60, 17 * 60)         # 4:00 to 5:00
]

# Define variables for meeting start and end times (in minutes)
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 60  # 1 hour in minutes

# Constraints to ensure meeting duration is one hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Ensure the meeting does not overlap with Anthony's busy schedule
for busy_start, busy_end in anthony_busy:
    solver.add(Or(start_time < busy_start, end_time > busy_end))

# Ensure the meeting does not overlap with Pamela's busy schedule
for busy_start, busy_end in pamela_busy:
    solver.add(Or(start_time < busy_start, end_time > busy_end))

# Ensure the meeting does not overlap with Zachary's busy schedule
for busy_start, busy_end in zachary_busy:
    solver.add(Or(start_time < busy_start, end_time > busy_end))

# Additional constraint: Pamela does not want to meet after 14:30
solver.add(start_time <= (14 * 60 + 30))

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