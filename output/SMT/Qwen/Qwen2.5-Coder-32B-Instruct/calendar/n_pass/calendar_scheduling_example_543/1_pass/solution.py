from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour
solver.add(end_time - start_time == 60)

# Meeting must be within work hours (9:00 to 17:00) on Monday
solver.add(start_time >= 9 * 60)
solver.add(end_time <= 17 * 60)
solver.add(day == "Monday")

# James' blocked times: 11:30 to 12:00, 14:30 to 15:00
solver.add(Or(start_time >= 12 * 60, end_time <= 11 * 60 + 30))
solver.add(Or(start_time >= 15 * 60, end_time <= 14 * 60 + 30))

# John's busy times: 9:30 to 11:00, 11:30 to 12:30, 12:30 to 13:30, 14:30 to 16:30
solver.add(Or(start_time >= 11 * 60, end_time <= 9 * 60 + 30))
solver.add(Or(start_time >= 12 * 60 + 30, end_time <= 11 * 60 + 30))
solver.add(Or(start_time >= 13 * 60, end_time <= 12 * 60 + 30))
solver.add(Or(start_time >= 16 * 60 + 30, end_time <= 14 * 60 + 30))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60

    print("SOLUTION:")
    print(f"Day: {model[day]}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")