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
    
    # The meeting must be 30 minutes long
    end_hour == start_hour + div(start_minute + meeting_duration, 60),
    end_minute == mod(start_minute + meeting_duration, 60),
    
    # Jack's busy times
    Or(start_hour * 60 + start_minute >= 1030, end_hour * 60 + end_minute <= 930),
    Or(start_hour * 60 + start_minute >= 1130, end_hour * 60 + end_minute <= 1100),
    Or(start_hour * 60 + start_minute >= 1300, end_hour * 60 + end_minute <= 1230),
    Or(start_hour * 60 + start_minute >= 1430, end_hour * 60 + end_minute <= 1400),
    Or(start_hour * 60 + start_minute >= 1630, end_hour * 60 + end_minute <= 1600),
    
    # Charlotte's busy times
    Or(start_hour * 60 + start_minute >= 1000, end_hour * 60 + end_minute <= 930),
    Or(start_hour * 60 + start_minute >= 1200, end_hour * 60 + end_minute <= 1030),
    Or(start_hour * 60 + start_minute >= 1330, end_hour * 60 + end_minute <= 1230),
    Or(start_hour * 60 + start_minute >= 1600, end_hour * 60 + end_minute <= 1400),
    
    # Jack's preference to avoid meetings after 12:30
    Or(start_hour * 60 + start_minute <= 1230, end_hour * 60 + end_minute <= 1230)
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