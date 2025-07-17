from z3 import *

# Define the time variables
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
constraints = [
    # Work hours constraint: 9:00 to 17:00
    start_hour >= 9,
    start_hour < 17,
    Or(start_hour < 16, And(start_hour == 16, start_minute == 0)),
    
    # Juan's availability: 10:30 to 15:30 and 16:00 to 16:00
    Or(And(start_hour == 10, start_minute >= 30), start_hour > 10),
    Or(And(start_hour == 15, start_minute <= 30), start_hour < 15),
    Or(And(start_hour == 16, start_minute >= 0), start_hour > 16),
    
    # Marilyn's availability: 9:00 to 11:00, 11:30 to 12:30, 13:00 to 17:00
    Or(And(start_hour == 9, start_minute >= 0), start_hour > 9),
    Or(And(start_hour == 11, start_minute <= 0), start_hour < 11),
    Or(And(start_hour == 11, start_minute >= 30), start_hour > 11),
    Or(And(start_hour == 12, start_minute <= 30), start_hour < 12),
    Or(And(start_hour == 13, start_minute >= 0), start_hour > 13),
    
    # Ronald's availability: 10:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 16:30 to 17:00
    Or(And(start_hour == 10, start_minute >= 30), start_hour > 10),
    Or(And(start_hour == 12, start_minute <= 0), start_hour < 12),
    Or(And(start_hour == 12, start_minute >= 30), start_hour > 12),
    Or(And(start_hour == 13, start_minute <= 0), start_hour < 13),
    Or(And(start_hour == 13, start_minute >= 30), start_hour > 13),
    Or(And(start_hour == 14, start_minute <= 0), start_hour < 14),
    Or(And(start_hour == 16, start_minute >= 30), start_hour > 16),
    
    # Meeting duration constraint
    end_hour * 60 + end_minute == start_hour * 60 + start_minute + meeting_duration,
    end_hour < 17,
    Or(end_hour > start_hour, And(end_hour == start_hour, end_minute > start_minute))
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