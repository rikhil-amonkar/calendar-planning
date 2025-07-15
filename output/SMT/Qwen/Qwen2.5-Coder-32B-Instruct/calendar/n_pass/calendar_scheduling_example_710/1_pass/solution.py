from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constants for the days
MONDAY = 0
TUESDAY = 1
WEDNESDAY = 2

# Define the constraints
constraints = []

# Cheryl's busy times
cheryl_busy_times = [
    (MONDAY, 9*60, 9*60 + 30),
    (MONDAY, 11*60 + 30, 13*60),
    (MONDAY, 15*60 + 30, 16*60),
    (TUESDAY, 15*60, 15*60 + 30)
]

# Kyle's busy times
kyle_busy_times = [
    (MONDAY, 9*60, 17*60),
    (TUESDAY, 9*60 + 30, 17*60),
    (WEDNESDAY, 9*60, 9*60 + 30),
    (WEDNESDAY, 10*60, 13*60),
    (WEDNESDAY, 13*60 + 30, 14*60),
    (WEDNESDAY, 14*60 + 30, 17*60)
]

# Meeting duration in minutes
meeting_duration = 30

# Define the constraints for the day
constraints.append(Or(day == MONDAY, day == TUESDAY))
constraints.append(day != WEDNESDAY)  # Cheryl can't meet on Wednesday

# Define the constraints for the start time
constraints.append(start_time >= 9*60)  # Start time must be after 9:00
constraints.append(start_time + meeting_duration <= 17*60)  # End time must be before 17:00

# Define the constraints for Cheryl's availability
for d, s, e in cheryl_busy_times:
    constraints.append(Or(start_time + meeting_duration <= s, start_time >= e))

# Define the constraints for Kyle's availability
for d, s, e in kyle_busy_times:
    constraints.append(Or(start_time + meeting_duration <= s, start_time >= e))

# Add constraints for the day
constraints.append(ForAll([day], Implies(day == MONDAY, And(start_time >= 9*60, start_time + meeting_duration <= 17*60))))
constraints.append(ForAll([day], Implies(day == TUESDAY, And(start_time >= 9*60, start_time + meeting_duration <= 17*60))))

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    # Convert day to string
    day_str = "Monday" if meeting_day == MONDAY else "Tuesday"
    
    # Convert time to HH:MM format
    start_time_str = f"{meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    end_time_str = f"{meeting_end_time // 60:02}:{meeting_end_time % 60:02}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")