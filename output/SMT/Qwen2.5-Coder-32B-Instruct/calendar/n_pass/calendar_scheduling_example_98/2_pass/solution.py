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
    
    # Work hours constraint
    Or(And(start_hour == 9, start_minute >= 0), start_hour > 9),
    Or(And(end_hour == 17, end_minute <= 0), end_hour < 17),
    
    # Juan's availability
    Or(And(start_hour == 10, start_minute >= 30), start_hour > 10),
    Or(And(end_hour == 15, end_minute <= 30), end_hour < 15),
    Or(And(end_hour == 16, end_minute <= 0), end_hour < 16),
    
    # Marilyn's availability
    Or(And(start_hour == 11, start_minute >= 30), start_hour > 11),
    Or(And(end_hour == 12, end_minute <= 30), end_hour < 12),
    Or(And(end_hour == 13, end_minute <= 0), end_hour < 13),
    
    # Ronald's availability
    Or(And(start_hour == 10, start_minute >= 30), start_hour > 10),
    Or(And(end_hour == 12, end_minute <= 0), end_hour < 12),
    Or(And(end_hour == 13, end_minute <= 0), end_hour < 13),
    Or(And(end_hour == 14, end_minute <= 0), end_hour < 14),
    Or(And(end_hour == 16, end_minute <= 30), end_hour < 16),
    
    # Meeting duration constraint
    end_hour == If(start_minute + meeting_duration >= 60, start_hour + 1, start_hour),
    end_minute == If(start_minute + meeting_duration >= 60, (start_minute + meeting_duration) % 60, start_minute + meeting_duration),
    
    # Ensure end time is within work hours
    Or(And(end_hour == 17, end_minute <= 0), end_hour < 17)
]

# Create the solver and add constraints
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