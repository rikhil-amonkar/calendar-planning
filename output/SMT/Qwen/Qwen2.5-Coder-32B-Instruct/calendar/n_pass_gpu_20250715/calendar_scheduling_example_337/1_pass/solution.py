from z3 import *

# Define the variables for the start time of the meeting
start_time = Int('start_time')

# Define the constraints
constraints = [
    # Meeting duration is 30 minutes
    And(start_time >= 9 * 60, start_time <= 16 * 60 - 30),  # Between 9:00 and 16:30
    
    # John's availability
    Or(start_time < 11 * 60 + 30, start_time >= 12 * 60),
    Or(start_time < 14 * 60, start_time >= 14 * 60 + 30),
    
    # Megan's availability
    Or(start_time < 12 * 60, start_time >= 12 * 60 + 30),
    Or(start_time < 14 * 60, start_time >= 15 * 60),
    Or(start_time < 15 * 60 + 30, start_time >= 16 * 60),
    
    # Brandon is available the whole day, so no additional constraints
    
    # Kimberly's availability
    Or(start_time < 9 * 60 + 30, start_time >= 9 * 60 + 60),
    Or(start_time < 10 * 60, start_time >= 10 * 60 + 30),
    Or(start_time < 11 * 60, start_time >= 14 * 60 + 30),
    Or(start_time < 15 * 60, start_time >= 16 * 60),
    Or(start_time < 16 * 60 + 30, start_time >= 17 * 60),
    
    # Sean's availability
    Or(start_time < 10 * 60, start_time >= 11 * 60),
    Or(start_time < 11 * 60 + 30, start_time >= 14 * 60),
    Or(start_time < 15 * 60, start_time >= 15 * 60 + 30),
    
    # Lori's availability
    Or(start_time < 9 * 60 + 30, start_time >= 10 * 60 + 30),
    Or(start_time < 12 * 60, start_time >= 13 * 60),
    Or(start_time < 14 * 60 + 30, start_time >= 16 * 60),
    Or(start_time < 16 * 60, start_time >= 16 * 60 + 30),
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_value = model[start_time].as_long()
    start_hour = start_time_value // 60
    start_minute = start_time_value % 60
    end_hour = start_hour + (start_minute + 30) // 60
    end_minute = (start_minute + 30) % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")