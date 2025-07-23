from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
constraints = [
    # Meeting must be on Monday
    day == 1,
    
    # Meeting must be between 9:00 and 17:00
    start_time >= 9 * 60,
    end_time <= 17 * 60,
    
    # Meeting duration is 30 minutes
    end_time == start_time + meeting_duration,
    
    # David's constraints: busy from 11:30 to 12:00, 14:30 to 15:00; prefers not to meet before 14:00
    Or(start_time >= 12 * 60, start_time < 11 * 60 + 30),
    Or(start_time >= 15 * 60, start_time < 14 * 60 + 30),
    start_time >= 14 * 60,
    
    # Douglas's constraints: busy from 9:30 to 10:00, 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:00
    Or(start_time >= 10 * 60, start_time < 9 * 60 + 30),
    Or(start_time >= 12 * 60, start_time < 11 * 60 + 30),
    Or(start_time >= 13 * 60 + 30, start_time < 13 * 60),
    Or(start_time >= 15 * 60, start_time < 14 * 60 + 30),
    
    # Ralph's constraints: busy from 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:30, 13:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00
    Or(start_time >= 9 * 60 + 30, start_time < 9 * 60),
    Or(start_time >= 11 * 60, start_time < 10 * 60),
    Or(start_time >= 12 * 30, start_time < 11 * 60 + 30),
    Or(start_time >= 15 * 60, start_time < 13 * 60 + 30),
    Or(start_time >= 16 * 60, start_time < 15 * 60 + 30),
    Or(start_time >= 17 * 60, start_time < 16 * 60 + 30),
    
    # Jordan's constraints: busy from 9:00 to 10:00, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:00, 15:30 to 17:00
    Or(start_time >= 10 * 60, start_time < 9 * 60),
    Or(start_time >= 12 * 30, start_time < 12 * 60),
    Or(start_time >= 13 * 30, start_time < 13 * 60),
    Or(start_time >= 15 * 60, start_time < 14 * 60 + 30),
    Or(start_time >= 17 * 60, start_time < 15 * 60 + 30),
]

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[start_time].as_long()
    end_time_minutes = model[end_time].as_long()
    start_time_formatted = f"{start_time_minutes // 60:02}:{start_time_minutes % 60:02}"
    end_time_formatted = f"{end_time_minutes // 60:02}:{end_time_minutes % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_formatted}\nEnd Time: {end_time_formatted}")
else:
    print("No solution found")