from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = []

# Meeting duration
meeting_duration = 60  # in minutes

# Work hours
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes

# Kayla's blocked times
kayla_blocked_times = [(10 * 60, 10 * 60 + 30), (14 * 60 + 30, 16 * 60)]

# Rebecca's blocked times
rebecca_blocked_times = [(9 * 60, 13 * 60), (13 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)]

# Constraints for the day
constraints.append(day == "Monday")

# Constraints for the time
constraints.append(start_time >= work_start)
constraints.append(end_time <= work_end)
constraints.append(end_time - start_time == meeting_duration)

# Constraints to avoid Kayla's blocked times
for block_start, block_end in kayla_blocked_times:
    constraints.append(Or(end_time <= block_start, start_time >= block_end))

# Constraints to avoid Rebecca's blocked times
for block_start, block_end in rebecca_blocked_times:
    constraints.append(Or(end_time <= block_start, start_time >= block_end))

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints can be satisfied
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print("SOLUTION:")
    print(f"Day: {model[day]}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found.")