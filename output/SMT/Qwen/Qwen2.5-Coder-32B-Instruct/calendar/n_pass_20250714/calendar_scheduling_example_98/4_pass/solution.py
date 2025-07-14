from z3 import *

# Define the variables for the meeting time
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
constraints = []

# The meeting duration is 30 minutes
constraints.append(end_hour * 60 + end_minute == start_hour * 60 + start_minute + 30)

# Meeting time must be within work hours (9:00 to 17:00)
constraints.append(start_hour * 60 + start_minute >= 9 * 60)
constraints.append(end_hour * 60 + end_minute <= 17 * 60)

# Ensure that end_hour and end_minute are correctly calculated
constraints.append(end_hour == If(start_minute + 30 >= 60, start_hour + 1, start_hour))
constraints.append(end_minute == If(start_minute + 30 >= 60, (start_minute + 30) % 60, start_minute + 30))

# Juan's availability: 9:00 to 10:30, 15:30 to 16:00
constraints.append(Or(start_hour * 60 + start_minute >= 10 * 60 + 30, end_hour * 60 + end_minute <= 10 * 60 + 30))
constraints.append(Or(start_hour * 60 + start_minute >= 16 * 60, end_hour * 60 + end_minute <= 15 * 60))

# Marilyn's availability: 11:00 to 11:30, 12:30 to 13:00
constraints.append(Or(start_hour * 60 + start_minute >= 11 * 60 + 30, end_hour * 60 + end_minute <= 11 * 60))
constraints.append(Or(start_hour * 60 + start_minute >= 13 * 60, end_hour * 60 + end_minute <= 12 * 60 + 30))

# Ronald's availability: 9:00 to 10:30, 12:00 to 12:30, 13:00 to 13:30, 14:00 to 16:30
constraints.append(Or(start_hour * 60 + start_minute >= 10 * 60 + 30, end_hour * 60 + end_minute <= 10 * 60))
constraints.append(Or(start_hour * 60 + start_minute >= 12 * 60 + 30, end_hour * 60 + end_minute <= 12 * 60))
constraints.append(Or(start_hour * 60 + start_minute >= 13 * 60 + 30, end_hour * 60 + end_minute <= 13 * 60))
constraints.append(Or(start_hour * 60 + start_minute >= 16 * 30, end_hour * 60 + end_minute <= 14 * 60))

# Ensure that start_hour and start_minute are valid
constraints.append(start_hour >= 9)
constraints.append(start_hour < 17)
constraints.append(start_minute >= 0)
constraints.append(start_minute < 60)

# Ensure that end_hour and end_minute are valid
constraints.append(end_hour >= 9)
constraints.append(end_hour < 17)
constraints.append(end_minute >= 0)
constraints.append(end_minute < 60)

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long():02}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long():02}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")