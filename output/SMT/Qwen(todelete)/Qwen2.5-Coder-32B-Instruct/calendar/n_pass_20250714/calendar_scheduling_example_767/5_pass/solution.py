from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the constraints for the day
constraints = [
    Or(day == 0, day == 1, day == 2),  # Day must be Monday, Tuesday, or Wednesday
    And(start_hour >= 9, start_hour <= 16),  # Meeting must start between 9:00 and 16:00
    start_minute == 0  # Meetings can only start on the hour
]

# Define Martha's constraints
martha_constraints = [
    Not(And(day == 0, start_hour >= 16)),  # Monday 16:00-17:00 is blocked
    Not(And(day == 1, start_hour == 15)),  # Tuesday 15:00-15:30 is blocked
    Not(And(day == 2, Or(start_hour == 10, start_hour == 14)))  # Wednesday 10:00-11:00 and 14:00-14:30 are blocked
]

# Define Beverly's constraints
beverly_constraints = [
    Not(And(day == 0, Or(start_hour < 13, start_hour >= 14))),  # Monday 9:00-13:30 and 14:00-17:00 are blocked
    Not(day == 1),  # Tuesday is fully blocked
    Not(And(day == 2, Or(start_hour < 9, start_hour >= 15, start_hour == 16)))  # Wednesday 9:30-15:30 and 16:30-17:00 are blocked
]

# Combine all constraints
all_constraints = constraints + martha_constraints + beverly_constraints

# Create a solver instance
solver = Solver()
solver.add(all_constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    
    # Convert day value to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[day_value]
    
    # Calculate end time
    end_hour = start_hour_value + 1
    end_minute = 0
    
    # Print the solution
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_hour_value:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")