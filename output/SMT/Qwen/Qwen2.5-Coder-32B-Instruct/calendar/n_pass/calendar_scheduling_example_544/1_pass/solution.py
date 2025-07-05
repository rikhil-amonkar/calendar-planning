from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = [
    # The meeting must be on Monday
    day == "Monday",
    
    # The meeting must be between 9:00 and 17:00
    start_time >= 9 * 60,
    end_time <= 17 * 60,
    
    # The meeting duration is 30 minutes
    end_time == start_time + 30,
    
    # Albert's busy times
    Or(start_time >= 11 * 60, end_time <= 10 * 60),  # 9:00 - 10:00
    Or(start_time >= 12 * 60, end_time <= 10 * 30),  # 10:30 - 12:00
    Or(start_time >= 16 * 60 + 30, end_time <= 15 * 60),  # 15:00 - 16:30
    
    # Albert cannot meet after 11:00
    end_time <= 11 * 60
]

# Create the solver
solver = Solver()

# Add the constraints to the solver
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    
    print(f"SOLUTION:\nDay: {model[day]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")