from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
constraints = [
    # Meeting must be on Monday
    day == 1,
    
    # Meeting must be between 9:00 and 17:00
    start_time >= 9 * 60,
    end_time <= 17 * 60,
    
    # Meeting duration is 30 minutes
    end_time == start_time + meeting_duration,
    
    # Adam's busy times: 14:00 to 15:00
    Or(start_time >= 15 * 60, end_time <= 14 * 60),
    
    # John's busy times: 13:00 to 13:30, 14:00 to 14:30, 15:30 to 16:00, 16:30 to 17:00
    Or(start_time >= 13 * 60 + 30, end_time <= 13 * 60),
    Or(start_time >= 14 * 60 + 30, end_time <= 14 * 60),
    Or(start_time >= 16 * 60, end_time <= 15 * 60 + 30),
    Or(start_time >= 17 * 60, end_time <= 16 * 60 + 30),
    
    # Stephanie's busy times: 9:30 to 10:00, 10:30 to 11:00, 11:30 to 16:00, 16:30 to 17:00
    Or(start_time >= 10 * 60, end_time <= 9 * 60 + 30),
    Or(start_time >= 11 * 60, end_time <= 10 * 60 + 30),
    Or(start_time >= 16 * 60, end_time <= 11 * 60 + 30),
    Or(start_time >= 17 * 60, end_time <= 16 * 60 + 30),
    
    # Anna's busy times: 9:30 to 10:00, 12:00 to 12:30, 13:00 to 15:30, 16:30 to 17:00
    Or(start_time >= 10 * 60, end_time <= 9 * 60 + 30),
    Or(start_time >= 12 * 60 + 30, end_time <= 12 * 60),
    Or(start_time >= 15 * 60 + 30, end_time <= 13 * 60),
    Or(start_time >= 17 * 60, end_time <= 16 * 60 + 30),
    
    # Anna prefers not to meet before 14:30
    start_time >= 14 * 60 + 30
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")