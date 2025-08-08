from z3 import *

# Define the time variables
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
constraints = [
    # Meeting must be on Monday
    day == 1,
    
    # Meeting must be between 9:00 and 17:00
    start_hour >= 9,
    start_hour < 17,
    Or(start_hour < 16, And(start_hour == 16, start_minute == 0)),
    
    # Meeting must be at least 30 minutes long
    end_hour == start_hour + (start_minute + meeting_duration) // 60,
    end_minute == (start_minute + meeting_duration) % 60,
    end_hour < 17,
    
    # Juan's availability
    Or(start_hour > 10, And(start_hour == 10, start_minute >= 30)),
    Or(end_hour < 15, And(end_hour == 15, end_minute <= 30)),
    
    # Marilyn's availability
    Or(start_hour > 11, And(start_hour == 11, start_minute >= 30)),
    Or(end_hour < 12, And(end_hour == 12, end_minute <= 30)),
    Or(start_hour > 13, And(start_hour == 13, start_minute >= 0)),
    Or(end_hour < 14, And(end_hour == 14, end_minute <= 0)),
    
    # Ronald's availability
    Or(start_hour > 10, And(start_hour == 10, start_minute >= 30)),
    Or(end_hour < 12, And(end_hour == 12, end_minute <= 0)),
    Or(start_hour > 13, And(start_hour == 13, start_minute >= 30)),
    Or(end_hour < 14, And(end_hour == 14, end_minute <= 0)),
    Or(start_hour > 16, And(start_hour == 16, start_minute >= 30)),
    Or(end_hour < 17, And(end_hour == 17, end_minute <= 0)),
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")