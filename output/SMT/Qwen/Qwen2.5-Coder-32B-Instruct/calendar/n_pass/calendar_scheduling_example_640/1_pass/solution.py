from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = [
    Or(day == 0, day == 1),  # Day can only be Monday or Tuesday
    start_time >= 0,  # Start time is at least 9:00
    start_time <= 480,  # End time is at most 17:00 (480 minutes from 9:00)
    start_time + 30 <= 480,  # Meeting must end before 17:00
]

# Bobby's busy times
bobby_busy_times = [
    (330, 360),  # Monday 14:30 to 15:00
    (0, 780),   # Tuesday 9:00 to 11:30
    (720, 750), # Tuesday 12:00 to 12:30
    (780, 900), # Tuesday 13:00 to 15:00
    (930, 1020) # Tuesday 15:30 to 17:00
]

# Michael's busy times
michael_busy_times = [
    (0, 60),    # Monday 9:00 to 10:00
    (60, 810),  # Monday 10:30 to 13:30
    (840, 900), # Monday 14:00 to 15:00
    (930, 1020),# Monday 15:30 to 17:00
    (0, 630),   # Tuesday 9:00 to 10:30
    (660, 720), # Tuesday 11:00 to 11:30
    (720, 840), # Tuesday 12:00 to 14:00
    (900, 960), # Tuesday 15:00 to 16:00
    (990, 1020)# Tuesday 16:30 to 17:00
]

# Add constraints for Bobby's busy times
for busy_start, busy_end in bobby_busy_times:
    constraints.append(Or(start_time + 30 <= busy_start, start_time >= busy_end))

# Add constraints for Michael's busy times
for busy_start, busy_end in michael_busy_times:
    constraints.append(Or(start_time + 30 <= busy_start, start_time >= busy_end))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time_minutes = model[start_time].as_long()
    meeting_start_time = f"{9 + meeting_start_time_minutes // 60}:{meeting_start_time_minutes % 60:02d}"
    meeting_end_time_minutes = meeting_start_time_minutes + 30
    meeting_end_time = f"{9 + meeting_end_time_minutes // 60}:{meeting_end_time_minutes % 60:02d}"
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")