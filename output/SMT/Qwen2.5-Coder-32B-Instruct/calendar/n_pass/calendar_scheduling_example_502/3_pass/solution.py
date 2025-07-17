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
    
    # The meeting must be half an hour long
    end_hour == If(start_minute + meeting_duration >= 60, start_hour + 1, start_hour),
    end_minute == If(start_minute + meeting_duration >= 60, (start_minute + meeting_duration) % 60, start_minute + meeting_duration),
    
    # Jack's busy times
    Or(start_hour * 60 + start_minute >= 10 * 60 + 30, start_hour * 60 + start_minute + meeting_duration <= 10 * 60 + 30),
    Or(start_hour * 60 + start_minute >= 11 * 60, start_hour * 60 + start_minute + meeting_duration <= 11 * 60 + 30),
    Or(start_hour * 60 + start_minute >= 12 * 60 + 30, start_hour * 60 + start_minute + meeting_duration <= 12 * 60 + 30),
    Or(start_hour * 60 + start_minute >= 14 * 60, start_hour * 60 + start_minute + meeting_duration <= 14 * 60 + 30),
    Or(start_hour * 60 + start_minute >= 16 * 60, start_hour * 60 + start_minute + meeting_duration <= 16 * 60),
    
    # Charlotte's busy times
    Or(start_hour * 60 + start_minute >= 10 * 60 + 30, start_hour * 60 + start_minute + meeting_duration <= 10 * 60 + 30),
    Or(start_hour * 60 + start_minute >= 12 * 60 + 30, start_hour * 60 + start_minute + meeting_duration <= 12 * 60 + 30),
    Or(start_hour * 60 + start_minute >= 14 * 60, start_hour * 60 + start_minute + meeting_duration <= 14 * 60 + 30),
    
    # Jack's preference to avoid meetings after 12:30
    Or(start_hour * 60 + start_minute <= 12 * 60 + 30, start_hour * 60 + start_minute + meeting_duration <= 12 * 60 + 30)
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