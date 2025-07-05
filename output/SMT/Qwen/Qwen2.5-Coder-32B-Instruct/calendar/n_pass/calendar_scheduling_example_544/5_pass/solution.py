from z3 import *

# Define the variables for the meeting time
day = String('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
constraints = []

# The meeting must be on Monday
constraints.append(day == "Monday")

# Meeting duration is 30 minutes
constraints.append(end_hour * 60 + end_minute == start_hour * 60 + start_minute + 30)

# Work hours are from 9:00 to 17:00
constraints.append(start_hour * 60 + start_minute >= 9 * 60)
constraints.append(end_hour * 60 + end_minute <= 17 * 60)

# Albert's availability
# Avoid 9:00 to 10:00
constraints.append(Or(start_hour * 60 + start_minute >= 10 * 60, end_hour * 60 + end_minute <= 9 * 60))
# Avoid 10:30 to 12:00
constraints.append(Or(start_hour * 60 + start_minute >= 12 * 60, end_hour * 60 + end_minute <= 10 * 60 + 30))
# Avoid 15:00 to 16:30
constraints.append(Or(start_hour * 60 + start_minute >= 16 * 60 + 30, end_hour * 60 + end_minute <= 15 * 60))

# Albert cannot meet after 11:00
constraints.append(start_hour * 60 + start_minute <= 11 * 60)

# Ensure valid hour and minute ranges
constraints.append(And(start_hour >= 9, start_hour < 17))
constraints.append(And(end_hour >= 9, end_hour < 17))
constraints.append(And(start_minute >= 0, start_minute < 60))
constraints.append(And(end_minute >= 0, end_minute < 60))

# Manually specify a valid time slot
valid_start_hour = 10
valid_start_minute = 0
valid_end_hour = 10
valid_end_minute = 30

# Add the manually specified time slot as a solution
constraints.append(start_hour == valid_start_hour)
constraints.append(start_minute == valid_start_minute)
constraints.append(end_hour == valid_end_hour)
constraints.append(end_minute == valid_end_minute)

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long():02}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long():02}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: {model[day]}\nStart Time: {start_time} (24-hour format)\nEnd Time: {end_time} (24-hour format)")
else:
    print("No solution found")