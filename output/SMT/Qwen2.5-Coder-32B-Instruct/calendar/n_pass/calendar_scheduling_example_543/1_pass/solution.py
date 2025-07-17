from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour
solver.add(end_time == start_time + 60)

# Meeting should be between 9:00 and 17:00 on Monday
solver.add(day == 1)  # Monday is represented by 1
solver.add(start_time >= 9 * 60)  # 9:00 in minutes
solver.add(end_time <= 17 * 60)  # 17:00 in minutes

# James's blocked times
solver.add(Or(start_time >= 11 * 60 + 30, end_time <= 12 * 60))  # 11:30 to 12:00
solver.add(Or(start_time >= 14 * 60 + 30, end_time <= 15 * 60))  # 14:30 to 15:00

# John's blocked times
solver.add(Or(start_time >= 9 * 60 + 30, end_time <= 11 * 60))  # 9:30 to 11:00
solver.add(Or(start_time >= 11 * 60 + 30, end_time <= 12 * 60))  # 11:30 to 12:00
solver.add(Or(start_time >= 12 * 60 + 30, end_time <= 13 * 60))  # 12:30 to 13:30
solver.add(Or(start_time >= 14 * 60 + 30, end_time <= 16 * 60 + 30))  # 14:30 to 16:30

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")