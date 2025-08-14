from z3 import *

# Define the variables for the day and time
day = Int('day')  # 1 for Monday, 2 for Tuesday, ..., 5 for Friday
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the constraints for the day
day_constraints = And(day >= 1, day <= 5)

# Define the constraints for the time (9:00 to 17:00)
time_constraints = And(start_hour >= 9, start_hour < 17, start_minute == 0)

# Define the meeting duration
meeting_duration = 30  # 30 minutes

# Define the availability constraints for Terry
terry_constraints = Or(
    And(day == 1, Or(And(start_hour == 9, start_minute == 0), And(start_hour == 11, start_minute == 0))),
    And(day == 2, Or(And(start_hour == 9, start_minute == 0), And(start_hour == 11, start_minute == 0), And(start_hour == 12, start_minute == 0))),
    And(day == 3, Or(And(start_hour == 9, start_minute == 0), And(start_hour == 10, start_minute == 0), And(start_hour == 12, start_minute == 0))),
    And(day == 4, Or(And(start_hour == 9, start_minute == 0), And(start_hour == 10, start_minute == 0), And(start_hour == 11, start_minute == 0))),
    And(day == 5, Or(And(start_hour == 9, start_minute == 0), And(start_hour == 10, start_minute == 0), And(start_hour == 11, start_minute == 0)))
)

# Define the availability constraints for Frances
frances_constraints = Or(
    And(day == 1, Or(And(start_hour == 9, start_minute == 0))),
    And(day == 2, Or(And(start_hour == 9, start_minute == 0))),
    And(day == 3, Or(And(start_hour == 9, start_minute == 0))),
    And(day == 4, Or(And(start_hour == 9, start_minute == 0))),
    And(day == 5, Or(And(start_hour == 9, start_minute == 0)))
)

# Avoid more meetings on Tuesday
avoid_tuesday = day != 2

# Combine all constraints
constraints = And(day_constraints, time_constraints, terry_constraints, frances_constraints, avoid_tuesday)

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    start_time = f"{start_hour_value:02}:{model[start_minute].as_long():02}"
    end_time = f"{(start_hour_value + meeting_duration // 60):02}:{(model[start_minute].as_long() + meeting_duration % 60):02}"
    
    # Adjust end time if it crosses an hour boundary
    if int(end_time.split(':')[1]) >= 60:
        end_time = f"{int(end_time.split(':')[0]) + 1}:{int(end_time.split(':')[1]) - 60:02}"
    
    # Map day number to day name
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_name = days[day_value - 1]
    
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")