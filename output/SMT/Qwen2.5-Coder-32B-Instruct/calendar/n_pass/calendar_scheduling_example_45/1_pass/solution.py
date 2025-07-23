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
    # Day constraint (Monday is represented as 1)
    day == 1,
    
    # Time constraints (9:00 to 17:00)
    start_hour >= 9,
    start_hour < 17,
    Or(start_hour < 16, And(start_hour == 16, start_minute == 0)),
    
    # Meeting duration constraint
    end_hour == If(start_minute + meeting_duration >= 60, start_hour + 1, start_hour),
    end_minute == (start_minute + meeting_duration) % 60,
    
    # Samuel's availability constraints
    Or(
        Or(start_hour < 9, And(start_hour == 9, start_minute < 0)),
        Or(start_hour > 10, And(start_hour == 10, start_minute >= 30)),
        Or(start_hour > 11, And(start_hour == 11, start_minute >= 30)),
        Or(start_hour > 12, And(start_hour == 12, start_minute >= 30)),
        Or(start_hour > 13, And(start_hour == 13, start_minute >= 30)),
        Or(start_hour > 14, And(start_hour == 14, start_minute >= 0)),
        Or(start_hour > 16, And(start_hour == 16, start_minute >= 30))
    )
]

# Create a solver instance
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")