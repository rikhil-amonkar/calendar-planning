from z3 import *

# Define the time variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
solver = Solver()

# All meetings must be on Monday
solver.add(day == "Monday")

# Meeting must be between 9:00 and 17:00
solver.add(start_time >= 9 * 60)
solver.add(end_time <= 17 * 60)

# Meeting duration is 30 minutes
solver.add(end_time == start_time + meeting_duration)

# Shirley's constraints
solver.add(Or(start_time >= 11 * 60 + 30, end_time <= 10 * 60 + 30))
solver.add(Or(start_time >= 12 * 60, end_time <= 12 * 30))

# Jacob's constraints
solver.add(Or(start_time >= 9 * 60 + 30, end_time <= 9 * 60))
solver.add(Or(start_time >= 10 * 30, end_time <= 10 * 60))
solver.add(Or(start_time >= 11 * 30, end_time <= 11 * 60))
solver.add(Or(start_time >= 13 * 30, end_time <= 12 * 30))
solver.add(Or(start_time >= 15 * 30, end_time <= 14 * 30))

# Stephen's constraints
solver.add(Or(start_time >= 12 * 60, end_time <= 11 * 30))
solver.add(Or(start_time >= 13 * 60, end_time <= 12 * 30 + 30))

# Margaret's constraints
solver.add(Or(start_time >= 9 * 60 + 30, end_time <= 9 * 60))
solver.add(Or(start_time >= 12 * 30, end_time <= 10 * 60 + 30))
solver.add(Or(start_time >= 13 * 30, end_time <= 13 * 60))
solver.add(Or(start_time >= 15 * 30, end_time <= 15 * 60))
solver.add(Or(start_time >= 16 * 30 + 30, end_time <= 16 * 30))

# Margaret's preference
solver.add(start_time >= 14 * 30)

# Mason's constraints
solver.add(Or(start_time >= 10 * 60, end_time <= 9 * 60))
solver.add(Or(start_time >= 11 * 30, end_time <= 10 * 60 + 30))
solver.add(Or(start_time >= 12 * 30, end_time <= 11 * 30 + 30))
solver.add(Or(start_time >= 13 * 30, end_time <= 13 * 60))
solver.add(Or(start_time >= 14 * 30, end_time <= 14 * 60))
solver.add(Or(start_time >= 16 * 30 + 30, end_time <= 16 * 30))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: {model[day]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")