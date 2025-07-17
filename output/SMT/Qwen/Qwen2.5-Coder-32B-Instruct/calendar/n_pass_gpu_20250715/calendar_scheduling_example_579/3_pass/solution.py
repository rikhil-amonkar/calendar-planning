from z3 import *

# Define the variables for the meeting start time
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the duration of the meeting
meeting_duration = 30  # in minutes

# Define the constraints for the meeting time
constraints = [
    # Meeting must be between 9:00 and 17:00
    start_hour >= 9,
    start_hour <= 16,
    Or(start_hour < 16, And(start_hour == 16, start_minute == 0)),
    
    # Christine's busy times: 11:00-11:30 and 15:00-15:30
    Or(
        Or(start_hour < 11, And(start_hour == 11, start_minute < 0)),
        Or(And(start_hour == 11, start_minute >= 30), start_hour > 11)
    ),
    Or(
        Or(start_hour < 15, And(start_hour == 15, start_minute < 0)),
        Or(And(start_hour == 15, start_minute >= 30), start_hour > 15)
    ),
    
    # Helen's busy times: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:30-16:00, 16:30-17:00
    Or(
        Or(start_hour < 9, And(start_hour == 9, start_minute < 30)),
        Or(And(start_hour == 10, start_minute >= 30), start_hour > 10)
    ),
    Or(
        Or(start_hour < 11, And(start_hour == 11, start_minute < 0)),
        Or(And(start_hour == 11, start_minute >= 30), start_hour > 11)
    ),
    Or(
        Or(start_hour < 12, And(start_hour == 12, start_minute < 0)),
        Or(And(start_hour == 12, start_minute >= 30), start_hour > 12)
    ),
    Or(
        Or(start_hour < 13, And(start_hour == 13, start_minute < 30)),
        Or(And(start_hour == 16, start_minute >= 0), start_hour > 16)
    ),
    Or(
        Or(start_hour < 16, And(start_hour == 16, start_minute < 30)),
        Or(And(start_hour == 17, start_minute >= 0), start_hour > 17)
    ),
    
    # Helen cannot meet after 15:00
    Or(start_hour < 15, And(start_hour == 15, start_minute < 0))
]

# Ensure the meeting does not overlap with Christine's busy times
constraints.append(
    Or(
        Or(start_hour < 11, And(start_hour == 11, start_minute < 0)),
        Or(And(start_hour == 11, start_minute >= 30), start_hour > 11)
    )
)
constraints.append(
    Or(
        Or(start_hour < 15, And(start_hour == 15, start_minute < 0)),
        Or(And(start_hour == 15, start_minute >= 30), start_hour > 15)
    )
)

# Ensure the meeting does not overlap with Helen's busy times
constraints.append(
    Or(
        Or(start_hour < 9, And(start_hour == 9, start_minute < 30)),
        Or(And(start_hour == 10, start_minute >= 30), start_hour > 10)
    )
)
constraints.append(
    Or(
        Or(start_hour < 11, And(start_hour == 11, start_minute < 0)),
        Or(And(start_hour == 11, start_minute >= 30), start_hour > 11)
    )
)
constraints.append(
    Or(
        Or(start_hour < 12, And(start_hour == 12, start_minute < 0)),
        Or(And(start_hour == 12, start_minute >= 30), start_hour > 12)
    )
)
constraints.append(
    Or(
        Or(start_hour < 13, And(start_hour == 13, start_minute < 30)),
        Or(And(start_hour == 16, start_minute >= 0), start_hour > 16)
    )
)
constraints.append(
    Or(
        Or(start_hour < 16, And(start_hour == 16, start_minute < 30)),
        Or(And(start_hour == 17, start_minute >= 0), start_hour > 17)
    )
)

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_h = model[start_hour].as_long()
    start_m = model[start_minute].as_long()
    end_h = start_h + (start_m + meeting_duration) // 60
    end_m = (start_m + meeting_duration) % 60
    
    # Format the solution
    start_time = f"{start_h:02}:{start_m:02}"
    end_time = f"{end_h:02}:{end_m:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")