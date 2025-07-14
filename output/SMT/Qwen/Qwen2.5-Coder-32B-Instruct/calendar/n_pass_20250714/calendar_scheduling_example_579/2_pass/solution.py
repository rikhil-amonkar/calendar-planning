from z3 import *

# Define the variables
day = "Monday"
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = [
    # Meeting duration is 30 minutes
    end_time == start_time + 30,
    
    # Meeting must be within work hours (9:00 to 17:00)
    start_time >= 9 * 60,
    end_time <= 17 * 60,
    
    # Christine's busy times
    Or(start_time >= 11 * 60 + 30, end_time <= 11 * 60),
    Or(start_time >= 15 * 60 + 30, end_time <= 15 * 60),
    
    # Helen's busy times
    Or(start_time >= 10 * 60 + 30, end_time <= 9 * 60 + 30),  # 9:30 to 10:30
    Or(start_time >= 11 * 60 + 30, end_time <= 11 * 60),
    Or(start_time >= 12 * 60 + 30, end_time <= 12 * 60),
    Or(start_time >= 13 * 60 + 30, end_time <= 13 * 60),
    Or(start_time >= 16 * 60, end_time <= 16 * 60 + 30),
    Or(start_time >= 16 * 60 + 30, end_time <= 16 * 60 + 30),
    
    # Helen can't meet after 15:00
    end_time <= 15 * 60
]

# Create a solver instance and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = model[end_time].as_long()
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start // 60}:{start % 60:02}\nEnd Time: {end // 60}:{end % 60:02}")
else:
    print("No solution found")