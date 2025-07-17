from z3 import *

# Define the time variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints for each participant
constraints = []

# Christine's busy times
constraints.append(Or(start_time >= 1030, end_time <= 930))
constraints.append(Or(start_time >= 1230, end_time <= 1200))
constraints.append(Or(start_time >= 1330, end_time <= 1300))
constraints.append(Or(start_time >= 1500, end_time <= 1430))
constraints.append(Or(start_time >= 1630, end_time <= 1600))

# Bobby's busy times
constraints.append(Or(start_time >= 1230, end_time <= 1200))
constraints.append(Or(start_time >= 1500, end_time <= 1430))

# Elizabeth's busy times
constraints.append(Or(start_time >= 930, end_time <= 900))
constraints.append(Or(start_time >= 1300, end_time <= 1130))
constraints.append(Or(start_time >= 1400, end_time <= 1330))
constraints.append(Or(start_time >= 1530, end_time <= 1500))
constraints.append(Or(start_time >= 1700, end_time <= 1600))

# Tyler's busy times
constraints.append(Or(start_time >= 1100, end_time <= 900))
constraints.append(Or(start_time >= 1230, end_time <= 1200))
constraints.append(Or(start_time >= 1330, end_time <= 1300))
constraints.append(Or(start_time >= 1600, end_time <= 1530))
constraints.append(Or(start_time >= 1700, end_time <= 1630))

# Edward's busy times
constraints.append(Or(start_time >= 930, end_time <= 900))
constraints.append(Or(start_time >= 1100, end_time <= 1000))
constraints.append(Or(start_time >= 1400, end_time <= 1130))
constraints.append(Or(start_time >= 1530, end_time <= 1430))
constraints.append(Or(start_time >= 1700, end_time <= 1600))

# Janice's preference
constraints.append(end_time <= 1300)

# Meeting must be within work hours
constraints.append(start_time >= 900)
constraints.append(end_time <= 1700)

# Meeting duration constraint
constraints.append(end_time == start_time + meeting_duration)

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_value = model[start_time].as_long()
    end_time_value = model[end_time].as_long()
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_value // 100}:{start_time_value % 100:02}\nEnd Time: {end_time_value // 100}:{end_time_value % 100:02}")
else:
    print("No solution found")