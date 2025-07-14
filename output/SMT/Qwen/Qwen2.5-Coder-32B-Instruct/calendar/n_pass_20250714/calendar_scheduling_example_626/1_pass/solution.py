from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes since 9:00

# Define the constraints
constraints = []

# Constraints for Patricia
# Monday: 10:00 to 10:30, 11:30 to 12:00, 13:00 to 13:30, 14:30 to 15:30, 16:00 to 16:30
constraints.append(Or(day != 0, Or(start_time < 60, start_time >= 90)))
constraints.append(Or(day != 0, Or(start_time < 80, start_time >= 120)))
constraints.append(Or(day != 0, Or(start_time < 150, start_time >= 180)))
constraints.append(Or(day != 0, Or(start_time < 210, start_time >= 330)))
constraints.append(Or(day != 0, Or(start_time < 360, start_time >= 390)))

# Tuesday: 10:00 to 10:30, 11:00 to 12:00, 14:00 to 16:00, 16:30 to 17:00
constraints.append(Or(day != 1, Or(start_time < 60, start_time >= 90)))
constraints.append(Or(day != 1, Or(start_time < 120, start_time >= 180)))
constraints.append(Or(day != 1, Or(start_time < 300, start_time >= 360)))
constraints.append(Or(day != 1, Or(start_time < 390, start_time >= 420)))

# Constraints for Jesse
# Monday: 9:00 to 17:00 (entire day is blocked)
constraints.append(day != 0)

# Tuesday: 11:00 to 11:30, 12:00 to 12:30, 13:00 to 14:00, 14:30 to 15:00, 15:30 to 17:00
constraints.append(Or(day != 1, Or(start_time < 120, start_time >= 150)))
constraints.append(Or(day != 1, Or(start_time < 180, start_time >= 210)))
constraints.append(Or(day != 1, Or(start_time < 240, start_time >= 300)))
constraints.append(Or(day != 1, Or(start_time < 330, start_time >= 390)))
constraints.append(Or(day != 1, Or(start_time < 390, start_time >= 480)))

# Meeting duration is 60 minutes
end_time = start_time + 60

# Meeting must be within work hours (9:00 to 17:00)
constraints.append(And(start_time >= 0, start_time < 480))  # 480 minutes from 9:00 to 17:00

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 60
    
    day_str = "Monday" if day_value == 0 else "Tuesday"
    start_time_str = f"{9 + start_time_value // 60}:{start_time_value % 60:02d}"
    end_time_str = f"{9 + end_time_value // 60}:{end_time_value % 60:02d}"
    
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")