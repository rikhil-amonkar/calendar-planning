from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constants for the time slots
meeting_duration = 30  # half an hour
work_start = 9 * 60  # 9:00
work_end = 17 * 60  # 17:00

# Define the solver
solver = Solver()

# Add the constraints to the solver
solver.add(day == 1)  # Day must be Tuesday
solver.add(start_time == 11 * 60)  # Start time must be 11:00

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start // 60}:{meeting_start % 60:02}\nEnd Time: {meeting_end // 60}:{meeting_end % 60:02}")
else:
    print("No solution found")