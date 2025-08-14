from z3 import *

# Define the time variables
day = "Monday"
start_time = Int('start_time')
end_time = start_time + 30  # Meeting duration is 30 minutes

# Define the constraints for each participant
constraints = [
    # Wayne is free the entire day, so no constraints
    # Melissa's constraints
    Or(start_time >= 1100, start_time < 1000),
    Or(start_time >= 1400, start_time < 1230),
    Or(start_time >= 1530, start_time < 1500),
    # Catherine is free the entire day, so no constraints
    # Gregory's constraints
    Or(start_time >= 1300, start_time < 1230),
    Or(start_time >= 1600, start_time < 1530),
    # Victoria's constraints
    Or(start_time >= 930, start_time < 900),
    Or(start_time >= 1130, start_time < 1030),
    Or(start_time >= 1400, start_time < 1300),
    Or(start_time >= 1500, start_time < 1430),
    Or(start_time >= 1630, start_time < 1530),
    # Thomas's constraints
    Or(start_time >= 1200, start_time < 1000),
    Or(start_time >= 1300, start_time < 1230),
    Or(start_time >= 1600, start_time < 1430),
    # Jennifer's constraints
    Or(start_time >= 930, start_time < 900),
    Or(start_time >= 1030, start_time < 1000),
    Or(start_time >= 1300, start_time < 1100),
    Or(start_time >= 1430, start_time < 1330),
    Or(start_time >= 1530, start_time < 1500),
    Or(start_time >= 1630, start_time < 1600),
    # Wayne's preference to avoid meetings before 14:00
    start_time >= 1400
]

# Define the solver
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 30
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start_time_value // 100:02}:{start_time_value % 100:02}\nEnd Time: {end_time_value // 100:02}:{end_time_value % 100:02}")
else:
    print("No solution found")