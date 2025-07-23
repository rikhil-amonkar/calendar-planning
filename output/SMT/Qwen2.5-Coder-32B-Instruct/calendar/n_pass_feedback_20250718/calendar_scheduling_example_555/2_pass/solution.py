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
    # Day constraint: Monday (assuming Monday is represented by 1)
    day == 1,
    
    # Work hours constraint: 9:00 to 17:00
    start_hour >= 9,
    start_hour < 17,
    Or(start_hour < 16, And(start_hour == 16, start_minute == 0)),
    
    # Evelyn's constraint: do not meet after 13:00
    Or(start_hour < 13, And(start_hour == 13, start_minute == 0)),
    
    # Randy's constraints: 9:00 to 10:30, 11:00 to 15:30, 16:00 to 17:00
    Or(
        Or(start_hour > 10, And(start_hour == 10, start_minute >= 30)),
        And(start_hour < 11),
        Or(start_hour > 15, And(start_hour == 15, start_minute >= 30)),
        And(start_hour < 16)
    ),
    
    # Meeting duration constraint
    end_hour == If(start_minute + meeting_duration >= 60, start_hour + 1, start_hour),
    end_minute == (start_minute + meeting_duration) % 60,
    
    # Ensure the meeting ends before 17:00
    Or(end_hour < 17, And(end_hour == 17, end_minute == 0)),
    
    # Ensure the meeting does not overlap with Randy's blocked times
    Or(
        Or(end_hour < 10, And(end_hour == 10, end_minute <= 30)),
        Or(start_hour > 10, And(start_hour == 10, start_minute >= 30)),
        Or(end_hour < 11, And(end_hour == 11, end_minute <= 0)),
        Or(start_hour > 11, And(start_hour == 11, start_minute >= 0)),
        Or(end_hour < 15, And(end_hour == 15, end_minute <= 30)),
        Or(start_hour > 15, And(start_hour == 15, start_minute >= 30)),
        Or(end_hour < 16, And(end_hour == 16, end_minute <= 0)),
        Or(start_hour > 16, And(start_hour == 16, start_minute >= 0))
    )
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_h = model[start_hour].as_long()
    start_m = model[start_minute].as_long()
    end_h = model[end_hour].as_long()
    end_m = model[end_minute].as_long()
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_h:02}:{start_m:02}\nEnd Time: {end_h:02}:{end_m:02}")
else:
    print("No solution found")