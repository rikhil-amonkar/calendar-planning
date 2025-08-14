from z3 import *

# Define the variables for the start time of the meeting
start_time = Int('start_time')

# Define the constraints for each participant's availability
constraints = [
    # Joe is available from 9:00 to 9:30, 10:00 to 10:30, 11:00 to 17:00
    Or(And(start_time >= 9 * 60, start_time < 9 * 60 + 30), And(start_time >= 10 * 60, start_time < 10 * 60 + 30), And(start_time >= 11 * 60, start_time < 17 * 60)),
    
    # Keith is available from 9:00 to 11:30, 12:00 to 15:00, 15:30 to 17:00
    Or(And(start_time >= 9 * 60, start_time < 11 * 60 + 30), And(start_time >= 12 * 60, start_time < 15 * 60), And(start_time >= 15 * 60 + 30, start_time < 17 * 60)),
    
    # Patricia is available from 9:30 to 13:00, 13:30 to 17:00
    Or(And(start_time >= 9 * 60 + 30, start_time < 13 * 60), And(start_time >= 13 * 60 + 30, start_time < 17 * 60)),
    
    # Nancy is available from 11:00 to 11:30, 16:30 to 17:00
    Or(And(start_time >= 11 * 60, start_time < 11 * 60 + 30), And(start_time >= 16 * 60 + 30, start_time < 17 * 60)),
    
    # Pamela is available from 9:00 to 10:00, 10:30 to 11:00, 12:30 to 13:00, 14:00 to 14:30, 15:00 to 15:30, 16:00 to 16:30
    Or(And(start_time >= 9 * 60, start_time < 10 * 60), And(start_time >= 10 * 60 + 30, start_time < 11 * 60), And(start_time >= 12 * 60 + 30, start_time < 13 * 60), 
       And(start_time >= 14 * 60, start_time < 14 * 60 + 30), And(start_time >= 15 * 60, start_time < 15 * 60 + 30), And(start_time >= 16 * 60, start_time < 16 * 60 + 30))
]

# The meeting duration is 30 minutes
meeting_duration = 30

# The meeting must start and end within working hours (9:00 to 17:00)
working_hours_start = 9 * 60
working_hours_end = 17 * 60
constraints.append(start_time >= working_hours_start)
constraints.append(start_time + meeting_duration <= working_hours_end)

# Create a solver instance
solver = Solver()

# Add all constraints to the solver
for constraint in constraints:
    solver.add(constraint)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[start_time].as_long()
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = (start_time_minutes + meeting_duration) // 60
    end_minute = (start_time_minutes + meeting_duration) % 60
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")