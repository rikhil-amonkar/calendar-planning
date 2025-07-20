from z3 import *

# Define the time variables
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = [
    # The meeting must be between 9:00 and 17:00
    start_time >= 9 * 60,
    end_time <= 17 * 60,
    # The meeting duration is 30 minutes
    end_time == start_time + 30,
    # Christine's busy times: 11:00 to 11:30, 15:00 to 15:30
    Or(start_time >= 11 * 60 + 30, end_time <= 11 * 60),
    Or(start_time >= 15 * 60 + 30, end_time <= 15 * 60),
    # Helen's busy times: 9:30 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:30 to 16:00, 16:30 to 17:00
    Or(start_time >= 9 * 60 + 30, end_time <= 10 * 60),
    Or(start_time >= 11 * 60 + 30, end_time <= 11 * 60),
    Or(start_time >= 12 * 60 + 30, end_time <= 12 * 60),
    Or(start_time >= 13 * 60 + 30, end_time <= 16 * 60),
    Or(start_time >= 16 * 60 + 30, end_time <= 16 * 60 + 30),
    # Helen can not meet on Monday after 15:00
    end_time <= 15 * 60
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