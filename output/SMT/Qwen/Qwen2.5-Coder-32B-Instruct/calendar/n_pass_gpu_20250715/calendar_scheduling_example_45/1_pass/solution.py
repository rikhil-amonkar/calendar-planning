from z3 import *

# Define the variables for the start time of the meeting
start_time = Int('start_time')

# Define the constraints for each participant's availability
constraints = [
    # Andrew is available all day from 9:00 to 17:00
    And(start_time >= 9*60, start_time + 30 <= 17*60),
    
    # Grace is also available all day from 9:00 to 17:00
    And(start_time >= 9*60, start_time + 30 <= 17*60),
    
    # Samuel's unavailability blocks
    Or(
        start_time >= 10*60 + 30,  # Samuel is free after 10:30
        And(start_time >= 12*60, start_time + 30 <= 13*60),  # Samuel is free from 12:00 to 13:00
        And(start_time >= 13*60 + 30, start_time + 30 <= 14*60),  # Samuel is free from 13:30 to 14:00
        And(start_time >= 16*60, start_time + 30 <= 16*60 + 30)  # Samuel is free from 16:00 to 16:30
    )
]

# Create a solver instance
solver = Solver()

# Add all constraints to the solver
for constraint in constraints:
    solver.add(constraint)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_minutes = model[start_time].as_long()
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = (start_minutes + 30) // 60
    end_minute = (start_minutes + 30) % 60
    
    # Format the output
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")