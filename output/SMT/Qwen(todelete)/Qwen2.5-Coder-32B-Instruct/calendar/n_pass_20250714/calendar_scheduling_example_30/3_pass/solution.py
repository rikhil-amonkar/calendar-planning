from z3 import *

# Define the time slots in 30-minute intervals from 9:00 to 17:00
time_slots = [9 + i * 0.5 for i in range(0, 16)]

# Define the variables for the start time of the meeting
start_time = Real('start_time')

# Define the constraints for each participant
constraints = []

# Jeffrey's constraints: 9:30-10:00, 10:30-11:00
constraints.append(Or(start_time < 9.5, start_time >= 10))
constraints.append(Or(start_time < 10.5, start_time >= 11))

# Virginia's constraints: 9:00-9:30, 10:00-10:30, 14:30-15:00, 16:00-16:30
constraints.append(Or(start_time < 9, start_time >= 9.5))
constraints.append(Or(start_time < 10, start_time >= 10.5))
constraints.append(Or(start_time < 14.5, start_time >= 15))
constraints.append(Or(start_time < 16, start_time >= 16.5))

# Melissa's constraints: 9:00-11:30, 12:00-12:30, 13:00-15:00, 16:00-17:00
constraints.append(Or(start_time < 9, start_time >= 11.5))
constraints.append(Or(start_time < 12, start_time >= 12.5))
constraints.append(Or(start_time < 13, start_time >= 15))
constraints.append(Or(start_time < 16, start_time >= 17))

# Melissa's preference: not after 14:00
constraints.append(start_time < 14)

# The meeting duration is 0.5 hours
end_time = start_time + 0.5

# Ensure the meeting ends before 17:00
constraints.append(end_time <= 17)

# Create a solver instance
solver = Solver()

# Add all constraints to the solver
for constraint in constraints:
    solver.add(constraint)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_decimal(2)
    end = float(start) + 0.5
    start_hour = int(start)
    start_minute = int((start % 1) * 60)
    end_hour = int(end)
    end_minute = int((end % 1) * 60)
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")