from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
solver = Solver()

# Meeting must be on Monday
solver.add(day == 1)

# Meeting must be between 9:00 and 17:00
solver.add(start_time >= 9 * 60)
solver.add(end_time <= 17 * 60)

# Meeting duration is 30 minutes
solver.add(end_time == start_time + meeting_duration)

# David's constraints: busy from 11:30 to 12:00, 14:30 to 15:00; prefers not to meet before 14:00
solver.add(Or(start_time >= 12 * 60, start_time < 11 * 60 + 30))
solver.add(Or(start_time >= 15 * 60, start_time < 14 * 60 + 30))
solver.add(start_time >= 14 * 60)

# Douglas's constraints: busy from 9:30 to 10:00, 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:00
solver.add(Or(start_time >= 10 * 60, start_time < 9 * 60 + 30))
solver.add(Or(start_time >= 12 * 60, start_time < 11 * 60 + 30))
solver.add(Or(start_time >= 13 * 60 + 30, start_time < 13 * 60))
solver.add(Or(start_time >= 15 * 60, start_time < 14 * 60 + 30))

# Ralph's constraints: busy from 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30, 13:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00
solver.add(Or(start_time >= 9 * 60 + 30, start_time < 9 * 60))
solver.add(Or(start_time >= 11 * 60, start_time < 10 * 60))
solver.add(Or(start_time >= 12 * 60 + 30, start_time < 11 * 60 + 30))
solver.add(Or(start_time >= 15 * 60, start_time < 13 * 60 + 30))
solver.add(Or(start_time >= 16 * 60, start_time < 15 * 60 + 30))
solver.add(Or(start_time >= 17 * 60, start_time < 16 * 60 + 30))

# Jordan's constraints: busy from 9:00 to 10:00, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:00, 15:30 to 17:00
solver.add(Or(start_time >= 10 * 60, start_time < 9 * 60))
solver.add(Or(start_time >= 12 * 60 + 30, start_time < 12 * 60))
solver.add(Or(start_time >= 13 * 60 + 30, start_time < 13 * 60))
solver.add(Or(start_time >= 15 * 60, start_time < 14 * 60 + 30))
solver.add(Or(start_time >= 17 * 60, start_time < 15 * 60 + 30))

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