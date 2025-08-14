from z3 import *

# Define the variables for the meeting time
day = "Monday"
start_time = Int('start_time')
end_time = Int('end_time')
meeting_duration = 60  # Meeting duration is 1 hour

# Define the constraints for each participant
constraints = []

# Evelyn is free the entire day
# No additional constraints needed for Evelyn

# Joshua's constraints
constraints.append(Or(start_time >= 1230, end_time <= 1100))
constraints.append(Or(start_time >= 1430, end_time <= 1330))
constraints.append(Or(start_time >= 1700, end_time <= 1630))

# Kevin is free the entire day
# No additional constraints needed for Kevin

# Gerald is free the entire day
# No additional constraints needed for Gerald

# Jerry's constraints
constraints.append(Or(start_time >= 930, end_time <= 900))
constraints.append(Or(start_time >= 1200, end_time <= 1030))
constraints.append(Or(start_time >= 1300, end_time <= 1230))
constraints.append(Or(start_time >= 1400, end_time <= 1300))
constraints.append(Or(start_time >= 1500, end_time <= 1430))
constraints.append(Or(start_time >= 1600, end_time <= 1530))

# Jesse's constraints
constraints.append(Or(start_time >= 930, end_time <= 900))
constraints.append(Or(start_time >= 1200, end_time <= 1030))
constraints.append(Or(start_time >= 1300, end_time <= 1230))
constraints.append(Or(start_time >= 1500, end_time <= 1430))
constraints.append(Or(start_time >= 1630, end_time <= 1530))

# Kenneth's constraints
constraints.append(Or(start_time >= 1230, end_time <= 1030))
constraints.append(Or(start_time >= 1400, end_time <= 1330))
constraints.append(Or(start_time >= 1500, end_time <= 1430))
constraints.append(Or(start_time >= 1600, end_time <= 1530))
constraints.append(Or(start_time >= 1700, end_time <= 1630))

# General constraints for the meeting time
constraints.append(start_time >= 900)  # Start time must be after 9:00
constraints.append(end_time <= 1700)   # End time must be before 17:00
constraints.append(end_time == start_time + meeting_duration)  # Meeting duration is 1 hour

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = model[end_time].as_long()
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start // 100}:{start % 100:02}\nEnd Time: {end // 100}:{end % 100:02}")
else:
    print("No solution found")