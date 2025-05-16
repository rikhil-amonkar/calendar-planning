from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define work hours in minutes from midnight
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM

# Define existing busy schedules for Harold in minutes
harold_busy_monday = [
    (9 * 60, 10 * 60),    # 9:00 to 10:00
    (10 * 60 + 30, 17 * 60)  # 10:30 to 5:00 PM
]

harold_busy_tuesday = [
    (9 * 60, 9 * 60 + 30),  # 9:00 to 9:30
    (10 * 60 + 30, 11 * 60),  # 10:30 to 11:30
    (12 * 60 + 30, 13 * 60 + 30),  # 12:30 to 1:30 PM
    (14 * 60 + 30, 15 * 60 + 30),  # 2:30 to 3:30 PM
    (16 * 60, 17 * 60)    # 4:00 to 5:00 PM
]

# Define variables for meeting start and end times (in minutes)
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 30  # in minutes

# Constraints to ensure meeting duration is half an hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Constraint to allow meeting only on Monday or Tuesday
solver.add(Or(day == 0, day == 1))

# Define availability functions for Monday and Tuesday
def add_busy_constraints(scheduler, busy_times):
    for busy_start, busy_end in busy_times:
        scheduler.add(Or(start_time < busy_start, end_time > busy_end))

# Ensure the meeting does not overlap with Harold's busy times
solver.add(If(day == 0, add_busy_constraints(solver, harold_busy_monday), 
               add_busy_constraints(solver, harold_busy_tuesday)))

# Additional constraints based on Harold's preferences
solver.add(If(day == 0, True, start_time >= (14 * 60 + 30)))  # Avoid Tuesday before 14:30

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    start = model[start_time].as_long()
    end = model[end_time].as_long()
    meeting_day = model[day].as_long()
    
    # Convert back to standard time for output
    start_hour = start // 60
    start_minute = start % 60
    end_hour = end // 60
    end_minute = end % 60
    
    day_name = "Monday" if meeting_day == 0 else "Tuesday"
    
    print(f"SOLUTION: Meeting on {day_name} from {start_hour:02}:{start_minute:02} to {end_hour:02}:{end_minute:02}")
else:
    print("No available time slot found.")