from z3 import *

# Define the time variables
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
constraints = [
    # Time constraints
    start_time >= 9 * 60,  # 9:00 in minutes
    end_time <= 17 * 60,   # 17:00 in minutes
    end_time == start_time + meeting_duration,
    
    # Bradley's constraints
    Or(start_time < 9 * 60 + 30, end_time <= 10 * 60),
    Or(start_time < 12 * 60 + 30, end_time <= 13 * 60),
    Or(start_time < 13 * 60 + 30, end_time <= 14 * 60),
    Or(start_time < 15 * 60 + 30, end_time <= 16 * 60),
    
    # Teresa's constraints
    Or(start_time < 10 * 60 + 30, end_time <= 11 * 60),
    Or(start_time < 12 * 0, end_time <= 12 * 60 + 30),
    Or(start_time < 13 * 0, end_time <= 13 * 60 + 30),
    Or(start_time < 14 * 60 + 30, end_time <= 15 * 60),
    
    # Elizabeth's constraints
    Or(start_time < 9 * 60, end_time <= 9 * 60 + 30),
    Or(start_time < 10 * 60 + 30, end_time <= 11 * 60 + 30),
    Or(start_time < 13 * 0, end_time <= 13 * 60 + 30),
    Or(start_time < 14 * 60 + 30, end_time <= 15 * 60),
    Or(start_time < 15 * 60 + 30, end_time <= 17 * 60),
    
    # Christian's constraints
    Or(start_time < 9 * 60, end_time <= 9 * 60 + 30),
    Or(start_time < 10 * 60 + 30, end_time <= 17 * 60),
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")