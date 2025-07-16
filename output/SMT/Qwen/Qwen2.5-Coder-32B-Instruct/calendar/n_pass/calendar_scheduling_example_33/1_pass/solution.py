from z3 import *

# Define the variables for the meeting time
day = String('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
solver.add(end_hour == start_hour + (start_minute + 30) // 60)
solver.add(end_minute == (start_minute + 30) % 60)

# Meeting must be within work hours (9:00 to 17:00)
solver.add(start_hour >= 9)
solver.add(end_hour <= 17)
solver.add(Or(end_hour > start_hour, And(end_hour == start_hour, end_minute > start_minute)))

# Lisa's schedule
solver.add(Not(And(start_hour <= 10, end_hour >= 9)))
solver.add(Not(And(start_hour <= 11, end_hour >= 10.5)))
solver.add(Not(And(start_hour <= 13, end_hour >= 12.5)))
solver.add(Not(And(start_hour <= 16.5, end_hour >= 16)))

# Bobby's schedule
solver.add(Not(And(start_hour <= 9.5, end_hour >= 9)))
solver.add(Not(And(start_hour <= 10.5, end_hour >= 10)))
solver.add(Not(And(start_hour <= 12, end_hour >= 11.5)))
solver.add(Not(And(start_hour <= 15.5, end_hour >= 15)))

# Bobby's preference to avoid meetings after 15:00
solver.add(end_hour <= 15)

# Randy's schedule
solver.add(Not(And(start_hour <= 10, end_hour >= 9.5)))
solver.add(Not(And(start_hour <= 11, end_hour >= 10.5)))
solver.add(Not(And(start_hour <= 12.5, end_hour >= 11.5)))
solver.add(Not(And(start_hour <= 13.5, end_hour >= 13)))
solver.add(Not(And(start_hour <= 15.5, end_hour >= 14.5)))
solver.add(Not(And(start_hour <= 16.5, end_hour >= 16)))

# Set the day to Monday
solver.add(day == "Monday")

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02d}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02d}"
    print(f"SOLUTION:\nDay: {model[day]}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")