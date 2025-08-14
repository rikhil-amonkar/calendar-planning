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

# The meeting must be between 9:00 and 17:00
constraints.append(start_hour >= 9)
constraints.append(end_hour <= 17)

# The meeting duration is 30 minutes
constraints.append(end_hour * 60 + end_minute == start_hour * 60 + start_minute + 30)

# Kimberly's availability
constraints.append(Or(
    Or(start_hour * 60 + start_minute < 10 * 60, end_hour * 60 + end_minute <= 10 * 60 + 30),
    Or(start_hour * 60 + start_minute < 11 * 60, end_hour * 60 + end_minute <= 11 * 60),
    Or(start_hour * 60 + start_minute < 16 * 60, end_hour * 60 + end_minute <= 16 * 60 + 30)
))

# Megan's preference: avoid meetings before 10:00
constraints.append(start_hour * 60 + start_minute >= 10 * 60)

# Marie's availability
constraints.append(Or(
    Or(start_hour * 60 + start_minute < 10 * 60, end_hour * 60 + end_minute <= 10 * 60),
    Or(start_hour * 60 + start_minute < 11 * 60 + 30, end_hour * 60 + end_minute <= 11 * 60 + 30),
    Or(start_hour * 60 + start_minute < 15 * 60, end_hour * 60 + end_minute <= 15 * 60),
    Or(start_hour * 60 + start_minute < 16 * 60, end_hour * 60 + end_minute <= 16 * 60 + 30)
))

# Diana's availability
constraints.append(Or(
    Or(start_hour * 60 + start_minute < 9 * 60 + 30, end_hour * 60 + end_minute <= 9 * 60 + 30),
    Or(start_hour * 60 + start_minute < 10 * 60 + 30, end_hour * 60 + end_minute <= 10 * 60 + 30),
    Or(start_hour * 60 + start_minute < 14 * 60 + 30, end_hour * 60 + end_minute <= 14 * 60 + 30),
    Or(start_hour * 60 + start_minute < 15 * 60 + 30, end_hour * 60 + end_minute <= 15 * 60 + 30)
))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02d}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02d}"
    print(f"SOLUTION:\nDay: {model[day]}\nStart Time: {start_time} (24-hour format)\nEnd Time: {end_time} (24-hour format)")
else:
    print("No solution found")