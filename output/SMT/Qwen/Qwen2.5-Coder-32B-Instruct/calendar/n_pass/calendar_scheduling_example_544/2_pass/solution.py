from z3 import *

# Define the variables for the meeting day and time
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = []

# Meeting duration is 30 minutes (0.5 hours)
meeting_duration = 30

# Constraints for the day (only Monday is considered here)
constraints.append(day == 1)  # Assuming Monday is represented as 1

# Constraints for Deborah (she is free the entire day)
# No additional constraints needed for Deborah

# Constraints for Albert
# Albert is busy from 9:00 to 10:00, 10:30 to 12:00, 15:00 to 16:30
constraints.append(Or(start_time >= 1000, end_time <= 900))  # Not during 9:00 to 10:00
constraints.append(Or(start_time >= 1200, end_time <= 1030))  # Not during 10:30 to 12:00
constraints.append(Or(start_time >= 1630, end_time <= 1500))  # Not during 15:00 to 16:30

# Albert cannot meet after 11:00
constraints.append(end_time <= 1100)

# Meeting must be within work hours (9:00 to 17:00)
constraints.append(start_time >= 900)
constraints.append(end_time <= 1700)

# Meeting duration constraint
constraints.append(end_time - start_time == meeting_duration)

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = model[end_time].as_long()

    # Convert times to HH:MM format
    start_hour = meeting_start_time // 100
    start_minute = meeting_start_time % 100
    end_hour = meeting_end_time // 100
    end_minute = meeting_end_time % 100

    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")