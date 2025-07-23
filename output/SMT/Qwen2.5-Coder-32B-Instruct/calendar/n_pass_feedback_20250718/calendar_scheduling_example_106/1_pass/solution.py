from z3 import *

# Define the time variables
day = String('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour
solver.add(end_hour == start_hour + 1)
solver.add(end_minute == start_minute)

# Meeting should be between 9:00 and 17:00 on Monday
solver.add(day == "Monday")
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(start_minute >= 0)
solver.add(start_minute < 60)

# Olivia's constraints
solver.add(Or(start_hour < 12, start_hour >= 13))
solver.add(Or(start_hour < 14, start_hour >= 15))
solver.add(start_hour < 16)

# Virginia's constraints
solver.add(start_hour >= 10)
solver.add(Or(start_hour < 11, start_hour >= 16))

# Paul's constraints
solver.add(start_hour >= 9)
solver.add(start_hour < 11)
solver.add(Or(start_hour < 13, start_hour >= 14))
solver.add(Or(start_hour < 16, start_hour >= 17))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")