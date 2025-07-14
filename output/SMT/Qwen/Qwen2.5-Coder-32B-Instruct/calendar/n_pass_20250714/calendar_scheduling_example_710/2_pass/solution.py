from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the constraints
constraints = []

# Constraints for the day
constraints.append(day == 1)  # Only consider Tuesday

# Constraints for the time
constraints.append(start_hour >= 9)
constraints.append(start_hour < 17)
constraints.append(start_minute == 0)  # We assume meetings start on the hour

# Cheryl's availability on Tuesday: 9:00-15:00 (excluding 15:00-15:30)
constraints.append(Or(start_hour < 15,
                     And(start_hour == 15, start_minute >= 30)))

# Kyle's availability on Tuesday: 9:30-17:00
constraints.append(Or(start_hour > 9,
                     And(start_hour == 9, start_minute >= 30)))

# Meeting duration is 30 minutes
end_hour = If(start_minute + 30 < 60, start_hour, start_hour + 1)
end_minute = (start_minute + 30) % 60

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday"][model[day].as_long()]
    meeting_start_hour = model[start_hour].as_long()
    meeting_start_minute = model[start_minute].as_long()
    meeting_end_hour = model[end_hour].as_long()
    meeting_end_minute = model[end_minute].as_long()
    
    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")