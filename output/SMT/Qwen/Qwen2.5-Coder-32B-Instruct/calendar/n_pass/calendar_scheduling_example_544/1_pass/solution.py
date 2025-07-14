from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Constants for the meeting duration
meeting_duration_hours = 0
meeting_duration_minutes = 30

# Constraints for the day
day_constraint = And(day == 1)  # Monday is represented as 1

# Constraints for the work hours
work_start_hour = 9
work_end_hour = 17

# Constraints for Deborah (free all day)
deborah_free = True

# Constraints for Albert
albert_blocked_times = [
    (9, 10),    # 9:00 to 10:00
    (10, 12),   # 10:30 to 12:00
    (15, 16)    # 15:00 to 16:30
]

albert_additional_constraint = start_hour < 11  # Albert can't meet after 11:00

# Define the constraints for the meeting time
constraints = [
    day_constraint,
    work_start_hour <= start_hour,
    start_hour < work_end_hour,
    Or(
        start_hour < albert_blocked_times[0][0],
        And(start_hour >= albert_blocked_times[0][1], start_hour < albert_blocked_times[1][0]),
        And(start_hour >= albert_blocked_times[1][1], start_hour < albert_blocked_times[2][0]),
        start_hour >= albert_blocked_times[2][1]
    ),
    albert_additional_constraint,
    start_minute == 0,  # We assume minutes are either 0 or 30
    Or(start_minute + meeting_duration_minutes < 60, And(start_hour + 1 < work_end_hour, start_minute == 0))
]

# Create a solver instance
solver = Solver()

# Add constraints to the solver
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday"
    meeting_start_hour = model[start_hour].as_long()
    meeting_start_minute = model[start_minute].as_long()
    meeting_end_hour = meeting_start_hour + meeting_duration_hours + (meeting_start_minute + meeting_duration_minutes) // 60
    meeting_end_minute = (meeting_start_minute + meeting_duration_minutes) % 60
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")