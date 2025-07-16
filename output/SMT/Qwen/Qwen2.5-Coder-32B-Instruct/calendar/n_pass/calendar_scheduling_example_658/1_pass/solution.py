from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constants for the problem
meeting_duration = 30  # in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes
tuesday_late_start = 10.5 * 60  # 10:30 in minutes

# Define the constraints
constraints = [
    Or(day == 0, day == 1),  # Day can only be Monday or Tuesday
    start_time >= work_start,  # Meeting must start after work starts
    start_time + meeting_duration <= work_end,  # Meeting must end before work ends
    
    # Shirley's constraints
    Or(start_time < 10.5 * 60, start_time >= 11 * 60),  # Avoid 10:30 - 11:00
    Or(start_time < 12 * 60, start_time >= 12.5 * 60),  # Avoid 12:00 - 12:30
    Or(start_time < 16 * 60, start_time >= 16.5 * 60),  # Avoid 16:00 - 16:30
    Or(day != 0, start_time < 9.5 * 60),  # Avoid 9:30 - 10:00 on Monday
    
    # Albert's constraints
    Or(day != 0, False),  # Busy all day on Monday
    Or(day != 1, Or(start_time < 9.5 * 60, start_time >= 11 * 60)),  # Avoid 9:30 - 11:00 on Tuesday
    Or(day != 1, Or(start_time < 11.5 * 60, start_time >= 12.5 * 60)),  # Avoid 11:30 - 12:30 on Tuesday
    Or(day != 1, Or(start_time < 13 * 60, start_time >= 16 * 60)),  # Avoid 13:00 - 16:00 on Tuesday
    Or(day != 1, Or(start_time < 16.5 * 60, start_time >= 17 * 60)),  # Avoid 16:30 - 17:00 on Tuesday
    
    # Shirley's preference
    Or(day != 1, start_time < tuesday_late_start)  # Prefer not to meet after 10:30 on Tuesday
]

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start = model[start_time].as_long()
    meeting_start_str = f"{int(meeting_start // 60):02}:{int(meeting_start % 60):02}"
    meeting_end_str = f"{int((meeting_start + meeting_duration) // 60):02}:{int((meeting_start + meeting_duration) % 60):02}"
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_str}\nEnd Time: {meeting_end_str}")
else:
    print("No solution found")