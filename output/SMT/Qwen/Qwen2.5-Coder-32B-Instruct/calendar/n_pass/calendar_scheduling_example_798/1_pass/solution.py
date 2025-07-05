from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the constraints
constraints = [
    # Day constraints
    Or(day == 1, day == 2, day == 3),
    
    # Work hours constraint (9:00 to 17:00)
    And(start_hour >= 9, start_hour <= 16),
    Or(start_hour < 16, And(start_hour == 16, start_minute == 0)),
    
    # Meeting duration constraint (30 minutes)
    Or(
        And(start_hour * 60 + start_minute + 30 <= 17 * 60),
        And(start_hour * 60 + start_minute + 30 > 17 * 60, start_hour * 60 + start_minute + 30 - 60 <= 17 * 60)
    ),
    
    # Nancy's availability constraints
    Not(And(day == 1, start_hour == 10, start_minute == 0)),  # 10:00 to 10:30
    Not(And(day == 1, start_hour == 11, start_minute == 30)),  # 11:30 to 12:30
    Not(And(day == 1, start_hour == 13, start_minute == 30)),  # 13:30 to 14:00
    Not(And(day == 1, start_hour == 14, start_minute == 30)),  # 14:30 to 15:30
    Not(And(day == 1, start_hour == 16, start_minute == 0)),   # 16:00 to 17:00
    Not(And(day == 2, start_hour == 9, start_minute == 30)),   # 9:30 to 10:30
    Not(And(day == 2, start_hour == 11, start_minute == 0)),   # 11:00 to 11:30
    Not(And(day == 2, start_hour == 12, start_minute == 0)),   # 12:00 to 12:30
    Not(And(day == 2, start_hour == 13, start_minute == 0)),   # 13:00 to 13:30
    Not(And(day == 2, start_hour == 15, start_minute == 30)),  # 15:30 to 16:00
    Not(And(day == 3, start_hour == 10, start_minute == 0)),   # 10:00 to 11:30
    Not(And(day == 3, start_hour == 13, start_minute == 30)),  # 13:30 to 16:00
    
    # Jose's availability constraints
    Not(And(day == 1, True)),                                 # 9:00 to 17:00
    Not(And(day == 2, True)),                                 # 9:00 to 17:00
    Not(And(day == 3, start_hour == 9, start_minute == 0)),   # 9:00 to 9:30
    Not(And(day == 3, start_hour == 10, start_minute == 0)),  # 10:00 to 12:30
    Not(And(day == 3, start_hour == 13, start_minute == 30)),  # 13:30 to 14:30
    Not(And(day == 3, start_hour == 15, start_minute == 0)),   # 15:00 to 17:00
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    start_minute_value = model[start_minute].as_long()
    end_hour_value = start_hour_value + (start_minute_value + 30) // 60
    end_minute_value = (start_minute_value + 30) % 60
    
    # Map day value to day name
    day_name = {1: "Monday", 2: "Tuesday", 3: "Wednesday"}[day_value]
    
    # Format the output
    start_time = f"{start_hour_value:02}:{start_minute_value:02}"
    end_time = f"{end_hour_value:02}:{end_minute_value:02}"
    
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")