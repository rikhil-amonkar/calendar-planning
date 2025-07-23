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
    # The meeting must be on Monday
    day == 1,
    
    # The meeting must be between 9:00 and 17:00
    start_hour >= 9,
    start_hour < 17,
    Or(start_hour < 16, And(start_hour == 16, start_minute == 0)),
    
    # The meeting must end before 17:00
    end_hour < 17,
    Or(end_hour > start_hour, And(end_hour == start_hour, end_minute > start_minute)),
    
    # The meeting must not overlap with Randy's blocked times
    Or(start_hour > 10, And(start_hour == 10, start_minute >= 30)),
    Or(end_hour < 11, And(end_hour == 11, end_minute <= 0)),
    Or(start_hour > 15, And(start_hour == 15, start_minute >= 30)),
    Or(end_hour < 16, And(end_hour == 16, end_minute <= 0)),
    
    # Evelyn does not want to meet after 13:00
    Or(start_hour < 13, And(start_hour == 13, start_minute == 0)),
    
    # The meeting duration is 30 minutes
    end_hour * 60 + end_minute == start_hour * 60 + start_minute + meeting_duration
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long():02}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long():02}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")