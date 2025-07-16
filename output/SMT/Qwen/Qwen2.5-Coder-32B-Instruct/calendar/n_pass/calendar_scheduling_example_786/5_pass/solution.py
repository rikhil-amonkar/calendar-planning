from z3 import *

# Define the variables for the day, start hour, and start minute
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the constraints for the meeting duration (30 minutes) and work hours (9:00 to 17:00)
constraints = [
    Or(day == 0, day == 1, day == 2),  # Day must be Monday, Tuesday, or Wednesday
    And(start_hour >= 9, start_hour < 17),  # Start hour must be between 9 and 16
    Or(And(start_hour == 16, start_minute == 0), start_hour < 16),  # If start hour is 16, start minute must be 0
    Or(start_minute == 0, start_minute == 30)  # Start minute must be 0 or 30
]

# Define Amy's busy times
amy_busy_times = [
    Not(And(day == 2, start_hour == 11, start_minute == 0)),  # Not Wednesday 11:00-11:30
    Not(And(day == 2, start_hour == 11, start_minute == 30)),
    Not(And(day == 2, start_hour == 13, start_minute == 30)),  # Not Wednesday 13:30-14:00
    Not(And(day == 2, start_hour == 14, start_minute == 0))
]

# Define Pamela's busy times
pamela_busy_times = [
    Not(And(day == 0, start_hour == 9, start_minute == 0)),  # Not Monday 9:00-10:30
    Not(And(day == 0, start_hour == 10, start_minute == 0)),
    Not(And(day == 0, start_hour == 10, start_minute == 30)),
    Not(And(day == 0, start_hour == 11, start_minute == 0)),
    Not(And(day == 0, start_hour == 16, start_minute == 0)),
    Not(And(day == 0, start_hour == 11, start_minute == 0)),  # Not Monday 11:00-16:30
    Not(And(day == 0, start_hour == 12, start_minute == 0)),
    Not(And(day == 0, start_hour == 13, start_minute == 0)),
    Not(And(day == 0, start_hour == 14, start_minute == 0)),
    Not(And(day == 0, start_hour == 15, start_minute == 0)),
    Not(And(day == 0, start_hour == 16, start_minute == 0)),
    Not(And(day == 1, start_hour == 9, start_minute == 0)),  # Not Tuesday 9:00-9:30
    Not(And(day == 1, start_hour == 9, start_minute == 30)),
    Not(And(day == 1, start_hour == 10, start_minute == 0)),  # Not Tuesday 10:00-17:00
    Not(And(day == 1, start_hour == 11, start_minute == 0)),
    Not(And(day == 1, start_hour == 12, start_minute == 0)),
    Not(And(day == 1, start_hour == 13, start_minute == 0)),
    Not(And(day == 1, start_hour == 14, start_minute == 0)),
    Not(And(day == 1, start_hour == 15, start_minute == 0)),
    Not(And(day == 1, start_hour == 16, start_minute == 0)),
    Not(And(day == 2, start_hour == 9, start_minute == 0)),  # Not Wednesday 9:00-9:30
    Not(And(day == 2, start_hour == 9, start_minute == 30)),
    Not(And(day == 2, start_hour == 10, start_minute == 0)),  # Not Wednesday 10:00-11:00
    Not(And(day == 2, start_hour == 11, start_minute == 0)),
    Not(And(day == 2, start_hour == 11, start_minute == 30)),  # Not Wednesday 11:30-13:30
    Not(And(day == 2, start_hour == 12, start_minute == 0)),
    Not(And(day == 2, start_hour == 13, start_minute == 0)),
    Not(And(day == 2, start_hour == 14, start_minute == 30)),  # Not Wednesday 14:30-15:00
    Not(And(day == 2, start_hour == 15, start_minute == 0)),
    Not(And(day == 2, start_hour == 16, start_minute == 0)),  # Not Wednesday 16:00-16:30
    Not(And(day == 2, start_hour == 16, start_minute == 30))
]

# Add Pamela's preference to avoid meetings on Monday and before 16:00 on Wednesday
pamela_preferences = [
    day != 0,  # Avoid Monday
    Or(day != 2, And(start_hour >= 16, start_minute == 0))  # If Wednesday, start at 16:00
]

# Combine all constraints
all_constraints = constraints + amy_busy_times + pamela_busy_times + pamela_preferences

# Create the solver and add the constraints
solver = Solver()
solver.add(all_constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    start_minute_value = model[start_minute].as_long()
    
    # Convert day value to string
    day_str = ["Monday", "Tuesday", "Wednesday"][day_value]
    
    # Format the start and end times
    start_time_str = f"{start_hour_value:02}:{start_minute_value:02}"
    end_time_str = f"{start_hour_value:02}:{(start_minute_value + 30) % 60:02}"
    if start_minute_value == 30:
        end_time_str = f"{start_hour_value + 1:02}:00"
    
    # Print the solution
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")