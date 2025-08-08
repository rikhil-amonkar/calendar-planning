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
    
    # Meeting must end before 17:00
    end_hour < 17,
    Or(end_hour > start_hour, And(end_hour == start_hour, end_minute > start_minute)),
    
    # Meeting must not overlap with Randy's blocked times
    Or(start_hour > 10, And(start_hour == 10, start_minute >= 30)),
    Or(end_hour < 11, And(end_hour == 11, end_minute <= 0)),
    Or(start_hour > 15, And(start_hour == 15, start_minute >= 30)),
    Or(end_hour < 16, And(end_hour == 16, end_minute <= 0)),
    
    # Evelyn does not want to meet after 13:00
    Or(start_hour < 13, And(start_hour == 13, start_minute == 0)),
    
    # Calculate end time based on start time and meeting duration
    end_hour == If(start_minute + meeting_duration >= 60, start_hour + 1, start_hour),
    end_minute == (start_minute + meeting_duration) % 60
]

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_h = model[start_hour].as_long()
    start_m = model[start_minute].as_long()
    end_h = model[end_hour].as_long()
    end_m = model[end_minute].as_long()
    
    # Format the solution
    solution = f"""SOLUTION:
Day: Monday
Start Time: {start_h:02}:{start_m:02}
End Time: {end_h:02}:{end_m:02}"""
    print(solution)
else:
    print("No solution found")