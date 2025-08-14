from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = [
    # The meeting must be on Monday
    day == 1,
    
    # The meeting must be within work hours
    start_time >= 9 * 60,
    end_time <= 17 * 60,
    
    # The meeting duration is 30 minutes
    end_time == start_time + 30,
    
    # Jose's constraints
    Or(start_time < 11 * 60, end_time > 11 * 60 + 30),
    Or(start_time < 12 * 60 + 30, end_time > 13 * 60),
    start_time < 15 * 60 + 30,  # Jose does not want to meet after 15:30
    
    # Keith's constraints
    Or(start_time < 14 * 60, end_time > 14 * 60 + 30),
    Or(start_time < 15 * 60, end_time > 15 * 60 + 30),
    
    # Logan's constraints
    Or(start_time < 10 * 60, end_time > 10 * 60),
    Or(start_time < 12 * 0, end_time > 12 * 60 + 30),
    Or(start_time < 15 * 0, end_time > 15 * 60 + 30),
    
    # Megan's constraints
    Or(start_time < 10 * 30, end_time > 10 * 60 + 30),
    Or(start_time < 11 * 60, end_time > 12 * 0),
    Or(start_time < 13 * 0, end_time > 13 * 30),
    Or(start_time < 14 * 30, end_time > 16 * 30),
    
    # Gary's constraints
    Or(start_time < 9 * 30, end_time > 9 * 60 + 30),
    Or(start_time < 10 * 0, end_time > 10 * 30),
    Or(start_time < 11 * 30, end_time > 13 * 0),
    Or(start_time < 13 * 30, end_time > 14 * 0),
    Or(start_time < 14 * 30, end_time > 16 * 30),
    
    # Bobby's constraints
    Or(start_time < 11 * 0, end_time > 11 * 30),
    Or(start_time < 12 * 0, end_time > 12 * 30),
    Or(start_time < 13 * 0, end_time > 16 * 0),
]

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")