from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the constraints
constraints = [
    # Day constraint: The meeting must be on Monday
    day == 1,
    
    # Time constraints: The meeting must be within work hours (9:00 to 17:00)
    start_hour >= 9,
    start_hour < 17,
    Or(start_hour < 16, And(start_hour == 16, start_minute < 30)),
    
    # Ensure start_minute is between 0 and 59
    start_minute >= 0,
    start_minute < 60,
    
    # Michael's constraints: 9:30-10:30, 15:00-15:30, 16:00-16:30
    Not(And(start_hour == 9, start_minute >= 30, start_minute < 60)),
    Not(And(start_hour == 10, start_minute >= 0, start_minute < 30)),
    Not(And(start_hour == 15, start_minute >= 0, start_minute < 30)),
    Not(And(start_hour == 16, start_minute >= 0, start_minute < 30)),
    
    # Eric's constraints: No constraints, available all day
    
    # Arthur's constraints: 9:00-12:00, 13:00-15:00, 15:30-16:00, 16:30-17:00
    Not(And(start_hour == 9, start_minute >= 0, start_minute < 60)),
    Not(And(start_hour == 10, start_minute >= 0, start_minute < 60)),
    Not(And(start_hour == 11, start_minute >= 0, start_minute < 60)),
    Not(And(start_hour == 12, start_minute >= 0, start_minute < 60)),
    Not(And(start_hour == 13, start_minute >= 0, start_minute < 60)),
    Not(And(start_hour == 14, start_minute >= 0, start_minute < 60)),
    Not(And(start_hour == 15, start_minute >= 0, start_minute < 30)),
    Not(And(start_hour == 15, start_minute >= 30, start_minute < 60)),
    Not(And(start_hour == 16, start_minute >= 0, start_minute < 30)),
    Not(And(start_hour == 16, start_minute >= 30, start_minute < 60))
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    start_minute_value = model[start_minute].as_long()
    
    # Calculate end time
    end_hour_value = start_hour_value + (start_minute_value + meeting_duration) // 60
    end_minute_value = (start_minute_value + meeting_duration) % 60
    
    # Format the output
    start_time = f"{start_hour_value:02}:{start_minute_value:02}"
    end_time = f"{end_hour_value:02}:{end_minute_value:02}"
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")