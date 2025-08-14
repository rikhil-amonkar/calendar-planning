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
solver.add(end_hour == If(start_minute + 30 >= 60, start_hour + 1, start_hour))
solver.add(end_minute == (start_minute + 30) % 60)

# Meeting must be within work hours (9:00 to 17:00)
solver.add(start_hour >= 9)
solver.add(end_hour <= 17)
solver.add(Or(end_hour > start_hour, And(end_hour == start_hour, end_minute > start_minute)))

# Lisa's schedule
solver.add(Not(And(start_hour * 60 + start_minute < 10 * 60, end_hour * 60 + end_minute > 9 * 60)))  # 9:00 to 10:00
solver.add(Not(And(start_hour * 60 + start_minute < 11 * 60 + 30, end_hour * 60 + end_minute > 10 * 60 + 30)))  # 10:30 to 11:30
solver.add(Not(And(start_hour * 60 + start_minute < 13 * 60, end_hour * 60 + end_minute > 12 * 60 + 30)))  # 12:30 to 13:00
solver.add(Not(And(start_hour * 60 + start_minute < 16 * 60 + 30, end_hour * 60 + end_minute > 16 * 60)))  # 16:00 to 16:30

# Bobby's schedule
solver.add(Not(And(start_hour * 60 + start_minute < 9 * 60 + 30, end_hour * 60 + end_minute > 9 * 60)))  # 9:00 to 9:30
solver.add(Not(And(start_hour * 60 + start_minute < 10 * 60 + 30, end_hour * 60 + end_minute > 10 * 60)))  # 10:00 to 10:30
solver.add(Not(And(start_hour * 60 + start_minute < 12 * 60, end_hour * 60 + end_minute > 11 * 30)))  # 11:30 to 12:00
solver.add(Not(And(start_hour * 60 + start_minute < 15 * 60 + 30, end_hour * 60 + end_minute > 15 * 60)))  # 15:00 to 15:30

# Bobby's preference to avoid meetings after 15:00
solver.add(end_hour * 60 + end_minute <= 15 * 60)

# Randy's schedule
solver.add(Not(And(start_hour * 60 + start_minute < 10 * 60 + 30, end_hour * 60 + end_minute > 9 * 60 + 30)))  # 9:30 to 10:00
solver.add(Not(And(start_hour * 60 + start_minute < 11 * 60, end_hour * 60 + end_minute > 10 * 60 + 30)))  # 10:30 to 11:00
solver.add(Not(And(start_hour * 60 + start_minute < 12 * 60 + 30, end_hour * 60 + end_minute > 11 * 30)))  # 11:30 to 12:30
solver.add(Not(And(start_hour * 60 + start_minute < 13 * 60, end_hour * 60 + end_minute > 13 * 60)))  # 13:00 to 13:30
solver.add(Not(And(start_hour * 60 + start_minute < 15 * 60 + 30, end_hour * 60 + end_minute > 14 * 60 + 30)))  # 14:30 to 15:30
solver.add(Not(And(start_hour * 60 + start_minute < 16 * 60 + 30, end_hour * 60 + end_minute > 16 * 60)))  # 16:00 to 16:30

# Set the day to Monday
solver.add(day == "Monday")

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02d}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02d}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")