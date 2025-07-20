from z3 import *

# Define the time variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
solver = Solver()

# All meetings must be on Monday between 9:00 and 17:00
solver.add(day == "Monday")
solver.add(start_time >= 9 * 60)  # 9:00 in minutes
solver.add(end_time <= 17 * 60)   # 17:00 in minutes
solver.add(end_time == start_time + meeting_duration)

# Jacob's busy times
solver.add(Or(start_time >= 13 * 60 + 30, end_time <= 14 * 60))
solver.add(Or(start_time >= 14 * 60 + 30, end_time <= 15 * 60))

# Diana's busy times
solver.add(Or(start_time >= 9 * 60 + 30, end_time <= 10 * 60))
solver.add(Or(start_time >= 11 * 60 + 30, end_time <= 12 * 60))
solver.add(Or(start_time >= 13 * 60, end_time <= 13 * 60 + 30))
solver.add(Or(start_time >= 16 * 60, end_time <= 16 * 60 + 30))

# Adam's busy times
solver.add(Or(start_time >= 9 * 60 + 30, end_time <= 10 * 60 + 30))
solver.add(Or(start_time >= 11 * 60, end_time <= 12 * 30))
solver.add(Or(start_time >= 15 * 60 + 30, end_time <= 16 * 60))

# Angela's busy times
solver.add(Or(start_time >= 9 * 60 + 30, end_time <= 10 * 60))
solver.add(Or(start_time >= 10 * 60 + 30, end_time <= 12 * 60))
solver.add(Or(start_time >= 13 * 60, end_time <= 15 * 30))
solver.add(Or(start_time >= 16 * 60, end_time <= 16 * 60 + 30))

# Dennis's busy times
solver.add(Or(start_time >= 9 * 60, end_time <= 9 * 60 + 30))
solver.add(Or(start_time >= 10 * 60 + 30, end_time <= 11 * 30))
solver.add(Or(start_time >= 13 * 60, end_time <= 15 * 60))
solver.add(Or(start_time >= 16 * 60 + 30, end_time <= 17 * 60))

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