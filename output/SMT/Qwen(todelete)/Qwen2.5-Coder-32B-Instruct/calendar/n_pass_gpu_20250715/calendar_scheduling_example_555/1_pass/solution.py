from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Constants for the problem
meeting_duration = 30  # in minutes
work_start = 9 * 60    # 9:00 AM in minutes from midnight
work_end = 17 * 60     # 5:00 PM in minutes from midnight

# Constraints
constraints = [
    # Meeting must be within work hours
    start_time >= work_start,
    end_time <= work_end,
    
    # Meeting duration constraint
    end_time == start_time + meeting_duration,
    
    # Randy's availability constraints
    Or(start_time >= 10 * 60 + 30, start_time < 9 * 60 + 30),  # Not between 9:00 and 10:30
    Or(start_time >= 15 * 60 + 30, start_time < 11 * 60),      # Not between 11:00 and 15:30
    Or(start_time >= 16 * 60, start_time < 16 * 60),            # Not between 16:00 and 17:00
    
    # Evelyn's preference constraint
    start_time < 13 * 60  # Not after 13:00
]

# Create a solver instance and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
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
    print("No solution found.")