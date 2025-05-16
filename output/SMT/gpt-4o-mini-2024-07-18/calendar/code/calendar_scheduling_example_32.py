from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define working hours in minutes from midnight
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM

# Define busy schedules for each participant
schedules = {
    'Emily': [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), 
              (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)],  # Busy on Monday
    'Melissa': [(9 * 60 + 30, 10 * 60), (14 * 60 + 30, 15 * 60)],  # Busy on Monday
    'Frank': [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), 
              (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60 + 30), 
              (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]  # Busy on Monday
}

# Define variables for the meeting start and end times (in minutes)
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 30  # in minutes

# Constraints to ensure meeting duration is half an hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Ensure the meeting does not overlap with any participant's busy schedules
for participant, busy_times in schedules.items():
    for busy_start, busy_end in busy_times:
        solver.add(Or(start_time < busy_start, end_time > busy_end))

# Additional constraint: Frank does not want to meet after 9:30
solver.add(start_time <= (9 * 60 + 30))  # 9:30 in minutes

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