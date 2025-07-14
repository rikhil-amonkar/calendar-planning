from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints for the meeting duration and working hours
constraints = [
    day == 1,  # Monday
    start_time >= 9 * 60,  # Start time should be after 9:00
    end_time <= 17 * 60,   # End time should be before 17:00
    end_time - start_time == 30  # Meeting duration is 30 minutes
]

# Constraints for Kimberly
constraints.append(Or(start_time < 10 * 60, end_time > 10 * 60 + 30))  # Not between 10:00 and 10:30
constraints.append(Or(start_time < 11 * 60, end_time > 12 * 60))      # Not between 11:00 and 12:00
constraints.append(Or(start_time < 16 * 60, end_time > 16 * 60 + 30))  # Not between 16:00 and 16:30

# Constraints for Megan
constraints.append(start_time >= 10 * 60)  # Avoid meetings before 10:00

# Constraints for Marie
constraints.append(Or(start_time < 10 * 60, end_time > 11 * 60))      # Not between 10:00 and 11:00
constraints.append(Or(start_time < 11 * 60 + 30, end_time > 15 * 60)) # Not between 11:30 and 15:00
constraints.append(Or(start_time < 16 * 60, end_time > 16 * 60 + 30))  # Not between 16:00 and 16:30

# Constraints for Diana
constraints.append(Or(start_time < 9 * 60 + 30, end_time > 10 * 60))      # Not between 9:30 and 10:00
constraints.append(Or(start_time < 10 * 60 + 30, end_time > 14 * 60 + 30)) # Not between 10:30 and 14:30
constraints.append(Or(start_time < 15 * 60 + 30, end_time > 17 * 60))     # Not between 15:30 and 17:00

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")