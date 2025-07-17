from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes since 9:00

# Define the constraints
constraints = [
    # Day must be between 0 and 2 (Monday to Wednesday)
    And(day >= 0, day <= 2),
    
    # Meeting duration is 60 minutes
    start_time + 60 <= 480,  # 480 minutes is 17:00 in 9:00-based minutes
    
    # Patrick is free all week, so no additional constraints for him
    
    # Roy's busy times:
    # Monday: 10:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00
    Or(day != 0,
       Not(And(start_time >= 60, start_time < 81)),  # 10:00-11:30
       Not(And(start_time >= 180, start_time < 210)),  # 12:00-13:00
       Not(And(start_time >= 300, start_time < 330)),  # 14:00-14:30
       Not(And(start_time >= 360, start_time < 480))),  # 15:00-17:00
    
    # Tuesday: 10:30-11:30, 12:00-14:30, 15:00-15:30, 16:00-17:00
    Or(day != 1,
       Not(And(start_time >= 63, start_time < 81)),  # 10:30-11:30
       Not(And(start_time >= 180, start_time < 270)),  # 12:00-14:30
       Not(And(start_time >= 360, start_time < 375)),  # 15:00-15:30
       Not(And(start_time >= 420, start_time < 480))),  # 16:00-17:00
    
    # Wednesday: 9:30-11:30, 12:30-14:00, 14:30-15:30, 16:30-17:00
    Or(day != 2,
       Not(And(start_time >= 30, start_time < 81)),  # 9:30-11:30
       Not(And(start_time >= 210, start_time < 240)),  # 12:30-14:00
       Not(And(start_time >= 270, start_time < 330)),  # 14:30-15:30
       Not(And(start_time >= 420, start_time < 480)))  # 16:30-17:00
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    
    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[day_value]
    
    # Convert start time to HH:MM format
    start_hour = 9 + start_time_value // 60
    start_minute = start_time_value % 60
    start_time_str = f"{start_hour:02}:{start_minute:02}"
    
    # Calculate end time
    end_time_value = start_time_value + 60
    end_hour = 9 + end_time_value // 60
    end_minute = end_time_value % 60
    end_time_str = f"{end_hour:02}:{end_minute:02}"
    
    # Print the solution
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")