from z3 import *

# Define the variables
day = String('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
constraints = [
    # The meeting must be on Monday
    day == "Monday",
    
    # The meeting duration is 30 minutes
    end_hour == start_hour,
    end_minute == start_minute + 30,
    Or(end_minute < 60, And(end_minute == 60, end_hour == start_hour + 1)),
    
    # Meeting must be within work hours (9:00 to 17:00)
    Or(And(start_hour == 9, start_minute >= 0), start_hour > 9),
    Or(And(end_hour == 17, end_minute <= 0), end_hour < 17),
    
    # David's constraints (busy from 11:30 to 12:00 and 14:30 to 15:00; prefers after 14:00)
    Or(
        Or(start_hour < 11, And(start_hour == 11, start_minute < 30)),
        Or(start_hour > 12, And(start_hour == 12, start_minute >= 0))
    ),
    Or(start_hour > 14, And(start_hour == 14, start_minute >= 30)),
    
    # Douglas's constraints (busy from 9:30 to 10:00, 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:00)
    Or(
        Or(start_hour < 9, And(start_hour == 9, start_minute < 30)),
        Or(start_hour > 10, And(start_hour == 10, start_minute >= 0))
    ),
    Or(
        Or(start_hour < 11, And(start_hour == 11, start_minute < 30)),
        Or(start_hour > 12, And(start_hour == 12, start_minute >= 0))
    ),
    Or(
        Or(start_hour < 13, And(start_hour == 13, start_minute < 0)),
        Or(start_hour > 13, And(start_hour == 13, start_minute >= 30))
    ),
    Or(
        Or(start_hour < 14, And(start_hour == 14, start_minute < 30)),
        Or(start_hour > 15, And(start_hour == 15, start_minute >= 0))
    ),
    
    # Ralph's constraints (busy from 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30, 13:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00)
    Or(
        Or(start_hour < 9, And(start_hour == 9, start_minute < 0)),
        Or(start_hour > 9, And(start_hour == 9, start_minute >= 30))
    ),
    Or(
        Or(start_hour < 10, And(start_hour == 10, start_minute < 0)),
        Or(start_hour > 11, And(start_hour == 11, start_minute >= 0))
    ),
    Or(
        Or(start_hour < 11, And(start_hour == 11, start_minute < 30)),
        Or(start_hour > 12, And(start_hour == 12, start_minute >= 30))
    ),
    Or(
        Or(start_hour < 13, And(start_hour == 13, start_minute < 30)),
        Or(start_hour > 15, And(start_hour == 15, start_minute >= 0))
    ),
    Or(
        Or(start_hour < 15, And(start_hour == 15, start_minute < 30)),
        Or(start_hour > 16, And(start_hour == 16, start_minute >= 0))
    ),
    Or(
        Or(start_hour < 16, And(start_hour == 16, start_minute < 30)),
        Or(start_hour > 17, And(start_hour == 17, start_minute >= 0))
    ),
    
    # Jordan's constraints (busy from 9:00 to 10:00, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:00, 15:30 to 17:00)
    Or(
        Or(start_hour < 9, And(start_hour == 9, start_minute < 0)),
        Or(start_hour > 10, And(start_hour == 10, start_minute >= 0))
    ),
    Or(
        Or(start_hour < 12, And(start_hour == 12, start_minute < 0)),
        Or(start_hour > 12, And(start_hour == 12, start_minute >= 30))
    ),
    Or(
        Or(start_hour < 13, And(start_hour == 13, start_minute < 0)),
        Or(start_hour > 13, And(start_hour == 13, start_minute >= 30))
    ),
    Or(
        Or(start_hour < 14, And(start_hour == 14, start_minute < 30)),
        Or(start_hour > 15, And(start_hour == 15, start_minute >= 0))
    ),
    Or(
        Or(start_hour < 15, And(start_hour == 15, start_minute < 30)),
        Or(start_hour > 17, And(start_hour == 17, start_minute >= 0))
    )
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