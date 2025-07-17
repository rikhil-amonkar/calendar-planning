from z3 import *

# Define the variables
day = Int('day')
start_time = Int('start_time')

# Define the constants for days and time
MONDAY, TUESDAY, WEDNESDAY, THURSDAY = 1, 2, 3, 4

# Constraints for Natalie
natalie_busy_times = [
    (MONDAY, 9*60, 9*60+30),
    (MONDAY, 10*60, 12*60),
    (MONDAY, 12*60+30, 13*60),
    (MONDAY, 14*60, 14*60+30),
    (MONDAY, 15*60, 16*60+30),
    (TUESDAY, 9*60, 9*60+30),
    (TUESDAY, 10*60, 10*60+30),
    (TUESDAY, 12*60+30, 14*60),
    (TUESDAY, 16*60, 17*60),
    (WEDNESDAY, 11*60, 11*60+30),
    (WEDNESDAY, 16*60, 16*60+30),
    (THURSDAY, 10*60, 11*60),
    (THURSDAY, 11*60+30, 15*60),
    (THURSDAY, 15*60+30, 16*60),
    (THURSDAY, 16*60+30, 17*60),
]

# Constraints for William
william_busy_times = [
    (MONDAY, 9*60+30, 11*60),
    (MONDAY, 11*60+30, 17*60),
    (TUESDAY, 9*60, 13*60),
    (TUESDAY, 13*60+30, 16*60),
    (WEDNESDAY, 9*60, 12*60+30),
    (WEDNESDAY, 13*60, 14*60+30),
    (WEDNESDAY, 15*60+30, 16*60),
    (WEDNESDAY, 16*60+30, 17*60),
    (THURSDAY, 9*60, 10*60+30),
    (THURSDAY, 11*60, 11*60+30),
    (THURSDAY, 12*60, 12*60+30),
    (THURSDAY, 13*60, 14*60),
    (THURSDAY, 15*60, 17*60),
]

# Create the solver
solver = Solver()

# Add constraints for the day
solver.add(Or(day == MONDAY, day == TUESDAY, day == WEDNESDAY, day == THURSDAY))

# Add constraints for the start time
solver.add(start_time >= 9*60)
solver.add(start_time <= 16*60)

# Add constraints to avoid busy times for Natalie
for d, s, e in natalie_busy_times:
    solver.add(Or(day != d, Or(start_time >= e, start_time + 60 <= s)))

# Add constraints to avoid busy times for William
for d, s, e in william_busy_times:
    solver.add(Or(day != d, Or(start_time >= e, start_time + 60 <= s)))

# Check if the constraints can be satisfied
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    
    # Convert day value to string
    day_str = {MONDAY: "Monday", TUESDAY: "Tuesday", WEDNESDAY: "Wednesday", THURSDAY: "Thursday"}[day_value]
    
    # Convert start time to HH:MM format
    start_hour = start_time_value // 60
    start_minute = start_time_value % 60
    start_time_str = f"{start_hour:02}:{start_minute:02}"
    
    # Calculate end time
    end_time_str = f"{(start_hour + 1):02}:{start_minute:02}"
    
    # Print the solution
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")