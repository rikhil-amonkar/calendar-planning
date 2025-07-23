from z3 import *

# Define the time variables
day = String('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
solver.add(end_hour == start_hour)
solver.add(end_minute == start_minute + 30)

# Meeting should be within work hours (9:00 to 17:00)
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(start_minute >= 0)
solver.add(start_minute < 60)

# Denise's availability
solver.add(Or(start_hour < 12, start_hour > 12, (start_hour == 12 and start_minute < 30)))
solver.add(Or(end_hour < 15, end_hour > 16, (end_hour == 15 and end_minute < 30)))

# Angela is available all day, so no additional constraints for her

# Natalie's availability
solver.add(Or(start_hour < 11, start_hour > 13, (start_hour == 11 and start_minute < 30)))
solver.add(Or(end_hour < 14, end_hour > 14, (end_hour == 14 and end_minute < 30)))
solver.add(Or(start_hour < 15, start_hour > 17, (start_hour == 15 and start_minute < 0)))

# Day is Monday
solver.add(day == "Monday")

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
    print(f"Day: {model[day]}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")