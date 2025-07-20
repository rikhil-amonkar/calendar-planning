from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = [
    # Day should be between 0 and 2
    And(day >= 0, day <= 2),
    
    # Start time should be between 0 and 480 (9:00 to 17:00 in minutes)
    And(start_time >= 0, start_time <= 480),
    
    # Meeting duration is 60 minutes
    start_time + 60 <= 480,
    
    # Judith's constraints
    Or(day != 0, Or(start_time < 720, start_time >= 750)),  # Not 12:00 to 12:30 on Monday
    Or(day != 2, Or(start_time < 690, start_time >= 720)),  # Not 11:30 to 12:00 on Wednesday
    
    # Timothy's constraints
    Or(day != 0, Or(start_time < 570, start_time >= 630)),  # Not 9:30 to 10:30 on Monday
    Or(day != 0, Or(start_time < 750, start_time >= 870)),  # Not 12:30 to 14:30 on Monday
    Or(day != 0, Or(start_time < 930, start_time >= 990)),  # Not 15:30 to 17:00 on Monday
    Or(day != 1, Or(start_time < 570, start_time >= 780)),  # Not 9:30 to 13:00 on Tuesday
    Or(day != 1, Or(start_time < 810, start_time >= 870)),  # Not 13:30 to 14:30 on Tuesday
    Or(day != 1, Or(start_time < 870, start_time >= 1020)), # Not 14:30 to 17:00 on Tuesday
    Or(day != 2, Or(start_time < 570, start_time >= 630)),  # Not 9:00 to 9:30 on Wednesday
    Or(day != 2, Or(start_time < 630, start_time >= 690)),  # Not 10:30 to 11:00 on Wednesday
    Or(day != 2, Or(start_time < 810, start_time >= 870)),  # Not 13:30 to 14:30 on Wednesday
    Or(day != 2, Or(start_time < 900, start_time >= 930)),  # Not 15:00 to 15:30 on Wednesday
    Or(day != 2, Or(start_time < 960, start_time >= 990)),  # Not 16:00 to 16:30 on Wednesday
    
    # Judith's preference to avoid more meetings on Monday
    day != 0,
    
    # Judith's preference to avoid meetings before 12:00 on Wednesday
    Or(day != 2, start_time >= 720)  # Not before 12:00 on Wednesday
]

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 60
    
    # Convert day and time to readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_hour = 9 + start_time_value // 60
    start_minute = start_time_value % 60
    end_hour = 9 + end_time_value // 60
    end_minute = end_time_value % 60
    
    print(f"SOLUTION:")
    print(f"Day: {days[day_value]}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")