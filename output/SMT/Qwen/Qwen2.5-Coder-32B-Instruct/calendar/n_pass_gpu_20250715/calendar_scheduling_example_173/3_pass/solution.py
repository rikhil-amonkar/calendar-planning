from z3 import *

# Define the variables for the meeting start time in minutes from 9:00
start_time = Int('start_time')

# Define the constraints for each participant
constraints = []

# Jacqueline's constraints
constraints.append(start_time < 540)  # before 9:30
constraints.append(Or(start_time >= 630, start_time < 660))  # not between 11:00 and 11:30
constraints.append(Or(start_time >= 780, start_time < 810))  # not between 12:30 and 13:00
constraints.append(Or(start_time >= 930, start_time < 960))  # not between 15:30 and 16:00

# Harold's constraints
constraints.append(start_time < 600)  # before 10:00
constraints.append(Or(start_time >= 780, start_time < 810))  # not between 13:00 and 13:30
constraints.append(start_time < 780)  # before 13:00 (Harold does not want to meet after 13:00)

# Arthur's constraints
constraints.append(start_time < 540)  # before 9:30
constraints.append(start_time < 750)  # before 12:30
constraints.append(Or(start_time >= 870, start_time < 900))  # not between 14:30 and 15:00
constraints.append(start_time < 930)  # before 15:30

# Kelly's constraints
constraints.append(start_time < 540)  # before 9:30
constraints.append(start_time < 600)  # before 10:00
constraints.append(Or(start_time >= 690, start_time < 720))  # not between 11:30 and 12:30
constraints.append(Or(start_time >= 840, start_time < 870))  # not between 14:00 and 15:00
constraints.append(start_time < 930)  # before 15:30

# Meeting duration is 30 minutes, so end_time is start_time + 30
end_time = start_time + 30

# The meeting must start between 9:00 and 17:00
constraints.append(start_time >= 540)  # 9:00 in minutes
constraints.append(end_time <= 1020)   # 17:00 in minutes

# Add the specific time slot constraint for 12:00 to 12:30
constraints.append(start_time == 720)  # 12:00 in minutes

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_minutes = model[start_time].as_long()
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = (start_minutes + 30) // 60
    end_minute = (start_minutes + 30) % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")