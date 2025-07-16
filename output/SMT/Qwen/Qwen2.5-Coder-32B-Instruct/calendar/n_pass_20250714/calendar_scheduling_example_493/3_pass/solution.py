from z3 import *

# Define the variables for the meeting time
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the solver
solver = Solver()

# Define the constraints for the meeting duration (30 minutes)
end_hour = If(start_minute + 30 >= 60, start_hour + 1, start_hour)
end_minute = (start_minute + 30) % 60

# Define the constraints for the meeting to be within work hours (9:00 to 17:00)
solver.add(start_hour >= 9)
solver.add(end_hour <= 17)
solver.add(Or(end_hour > start_hour, And(end_hour == start_hour, end_minute > start_minute)))

# Define the constraints for each participant's availability
# Tyler and Kelly are free the entire day, so no additional constraints needed for them

# Stephanie's constraints
solver.add(Or(start_hour * 60 + start_minute < 11 * 60,
              end_hour * 60 + end_minute > 11 * 60 + 30))
solver.add(Or(start_hour * 60 + start_minute < 14 * 60 + 30,
              end_hour * 60 + end_minute > 15 * 60))

# Hannah is free the entire day, so no additional constraints needed for her

# Joe's constraints
solver.add(Or(start_hour * 60 + start_minute < 9 * 60 + 30,
              end_hour * 60 + end_minute > 12 * 60))
solver.add(Or(start_hour * 60 + start_minute < 14 * 60,
              end_hour * 60 + end_minute > 17 * 60))

# Diana's constraints
solver.add(Or(start_hour * 60 + start_minute < 10 * 60 + 30,
              end_hour * 60 + end_minute > 11 * 60 + 30))
solver.add(Or(start_hour * 60 + start_minute < 12 * 60,
              end_hour * 60 + end_minute > 13 * 60))
solver.add(Or(start_hour * 60 + start_minute < 14 * 60,
              end_hour * 60 + end_minute > 15 * 60 + 30))
solver.add(Or(start_hour * 60 + start_minute < 16 * 60,
              end_hour * 60 + end_minute > 17 * 60))

# Deborah's constraints
solver.add(Or(start_hour * 60 + start_minute < 10 * 60,
              end_hour * 60 + end_minute > 10 * 60 + 30))
solver.add(Or(start_hour * 60 + start_minute < 12 * 60,
              end_hour * 60 + end_minute > 13 * 60))
solver.add(Or(start_hour * 60 + start_minute < 13 * 60,
              end_hour * 60 + end_minute > 14 * 60))
solver.add(Or(start_hour * 60 + start_minute < 15 * 60,
              end_hour * 60 + end_minute > 15 * 60 + 30))
solver.add(Or(start_hour * 60 + start_minute < 16 * 60,
              end_hour * 60 + end_minute > 16 * 60 + 30))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")