from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
constraints = []

# Work hours constraint
constraints.append(And(start_time >= 9*60, start_time <= 17*60 - 30))

# Day constraint
constraints.append(Or(day == 0, day == 1, day == 2))

# John's preference to avoid meetings on Monday after 14:30
constraints.append(Or(day != 0, start_time <= 14*60 + 30))

# Jennifer's schedule constraints
# Monday: 9:00 to 11:00, 11:30 to 13:00, 13:30 to 14:30, 15:00 to 17:00
constraints.append(Or(day != 0, Or(start_time < 9*60, start_time >= 11*60)))
constraints.append(Or(day != 0, Or(start_time < 11*60 + 30, start_time >= 13*60)))
constraints.append(Or(day != 0, Or(start_time < 13*60 + 30, start_time >= 14*60 + 30)))
constraints.append(Or(day != 0, Or(start_time < 15*60, start_time >= 17*60)))

# Tuesday: 9:00 to 11:30, 12:00 to 17:00
constraints.append(Or(day != 1, Or(start_time < 9*60, start_time >= 11*60 + 30)))
constraints.append(Or(day != 1, Or(start_time < 12*60, start_time >= 17*60)))

# Wednesday: 9:00 to 11:30, 12:00 to 12:30, 13:00 to 14:00, 14:30 to 16:00, 16:30 to 17:00
constraints.append(Or(day != 2, Or(start_time < 9*60, start_time >= 11*60 + 30)))
constraints.append(Or(day != 2, Or(start_time < 12*60, start_time >= 12*60 + 30)))
constraints.append(Or(day != 2, Or(start_time < 13*60, start_time >= 14*60)))
constraints.append(Or(day != 2, Or(start_time < 14*60 + 30, start_time >= 16*60)))
constraints.append(Or(day != 2, Or(start_time < 16*60 + 30, start_time >= 17*60)))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 30
    
    # Convert day number to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[day_value]
    
    # Convert time from minutes to HH:MM format
    start_time_str = f"{start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{end_time_value // 60:02}:{end_time_value % 60:02}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")