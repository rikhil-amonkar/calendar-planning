from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = [
    # The meeting must be on Monday
    day == "Monday",
    
    # The meeting duration is 30 minutes
    end_time == start_time + 30,
    
    # Meeting time must be within working hours (9:00 to 17:00)
    start_time >= 9 * 60,
    end_time <= 17 * 60,
    
    # Denise's unavailability
    Or(start_time >= 12 * 60 + 30, end_time <= 12 * 60),
    Or(start_time >= 16 * 60, end_time <= 15 * 60 + 30),
    
    # Angela is available all day, so no additional constraints for her
    
    # Natalie's unavailability
    Or(start_time >= 11 * 60 + 30, end_time <= 9 * 60),
    Or(start_time >= 13 * 60, end_time <= 12 * 60),
    Or(start_time >= 14 * 60 + 30, end_time <= 14 * 60),
    Or(start_time >= 17 * 60, end_time <= 15 * 60)
]

# Create a solver instance
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    
    print(f"SOLUTION:\nDay: {model[day]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")