from z3 import *

# Define the time variables
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
constraints = [
    # The meeting must be between 9:00 and 17:00
    start_hour >= 9,
    start_hour < 17,
    Or(start_hour < 16, And(start_hour == 16, start_minute == 0)),
    
    # The meeting must not overlap with Randy's blocked times
    Or(start_hour > 10, And(start_hour == 10, start_minute >= 30)),
    Or(start_hour * 60 + start_minute >= 11 * 60, start_hour * 60 + start_minute < 15 * 60),
    Or(start_hour > 15, And(start_hour == 15, start_minute >= 30)),
    Or(start_hour * 60 + start_minute >= 16 * 60, start_hour * 60 + start_minute < 17 * 60),
    
    # Evelyn does not want to meet after 13:00
    Or(start_hour < 13, And(start_hour == 13, start_minute == 0)),
    
    # The meeting duration is 30 minutes
    (start_hour * 60 + start_minute + meeting_duration) // 60 == start_hour + (start_minute + meeting_duration) // 60,
    (start_hour * 60 + start_minute + meeting_duration) % 60 == (start_minute + meeting_duration) % 60
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long():02}:{model[start_minute].as_long():02}"
    end_time = f"{(model[start_hour].as_long() + (model[start_minute].as_long() + meeting_duration) // 60):02}:{(model[start_minute].as_long() + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")