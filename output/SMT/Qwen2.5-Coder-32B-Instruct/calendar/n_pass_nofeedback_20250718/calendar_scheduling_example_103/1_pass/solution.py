from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
constraints = [
    # Day constraint: Monday (assuming Monday is represented by 1)
    day == 1,
    
    # Time constraints: between 9:00 and 17:00
    start_time >= 9 * 60,  # 9:00 in minutes
    end_time <= 17 * 60,   # 17:00 in minutes
    
    # Meeting duration constraint
    end_time == start_time + meeting_duration,
    
    # Diane's constraints
    Or(start_time >= 10 * 60, end_time <= 9 * 60 + 30),  # 10:00 in minutes
    Or(start_time >= 15 * 60, end_time <= 14 * 60 + 30),  # 15:00 in minutes
    
    # Jack's constraints
    Or(start_time >= 14 * 60, end_time <= 13 * 60 + 30),  # 14:00 in minutes
    Or(start_time >= 15 * 60, end_time <= 14 * 60 + 30),  # 15:00 in minutes
    
    # Eugene's constraints
    Or(start_time >= 10 * 60 + 30, end_time <= 9 * 60),  # 10:30 in minutes
    Or(start_time >= 11 * 60 + 30, end_time <= 10 * 60 + 30),  # 11:30 in minutes
    Or(start_time >= 14 * 60 + 30, end_time <= 12 * 60),  # 14:30 in minutes
    Or(start_time >= 16 * 60 + 30, end_time <= 15 * 60),  # 16:30 in minutes
    
    # Patricia's constraints
    Or(start_time >= 10 * 60 + 30, end_time <= 9 * 60 + 30),  # 10:30 in minutes
    Or(start_time >= 12 * 60, end_time <= 11 * 60),  # 12:00 in minutes
    Or(start_time >= 14 * 60, end_time <= 12 * 60 + 30),  # 14:00 in minutes
    Or(start_time >= 16 * 60 + 30, end_time <= 15 * 60),  # 16:30 in minutes
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[start_time].as_long()
    end_time_minutes = model[end_time].as_long()
    
    # Convert minutes back to HH:MM format
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")