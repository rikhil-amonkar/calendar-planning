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

# Anthony's busy times
solver.add(Or(start_hour < 9, start_hour > 10, (start_hour == 10 and start_minute >= 0)))
solver.add(Or(start_hour < 12, start_hour > 13, (start_hour == 13 and start_minute >= 0)))
solver.add(Or(start_hour < 16, start_hour > 16, (start_hour == 16 and start_minute >= 30)))

# Pamela's busy times and preference
solver.add(Or(start_hour < 9, start_hour > 10, (start_hour == 10 and start_minute >= 0)))
solver.add(Or(start_hour < 14, start_hour > 16, (start_hour == 16 and start_minute >= 30)))
solver.add(start_hour < 14)  # Pamela's preference not to meet after 14:30

# Zachary's busy times
solver.add(Or(start_hour < 9, start_hour > 11, (start_hour == 11 and start_minute >= 30)))
solver.add(Or(start_hour < 12, start_hour > 12, (start_hour == 12 and start_minute >= 30)))
solver.add(Or(start_hour < 13, start_hour > 13, (start_hour == 13 and start_minute >= 30)))
solver.add(Or(start_hour < 14, start_hour > 14, (start_hour == 14 and start_minute >= 30)))
solver.add(Or(start_hour < 16, start_hour > 17, (start_hour == 17 and start_minute >= 0)))

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