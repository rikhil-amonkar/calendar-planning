from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = []

# The meeting must be on Monday
constraints.append(day == 1)

# The meeting duration is 30 minutes
constraints.append(end_time == start_time + 30)

# Meeting must be within work hours (9:00 to 17:00)
constraints.append(start_time >= 900)
constraints.append(end_time <= 1700)

# Samuel's blocked times
samuel_blocked_times = [
    (900, 1030),
    (1130, 1200),
    (1300, 1330),
    (1400, 1600),
    (1630, 1700)
]

# Constraints to avoid Samuel's blocked times
for start, end in samuel_blocked_times:
    constraints.append(Or(end_time <= start, start_time >= end))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = model[end_time].as_long()

    # Format the output
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time_value // 100:02}:{start_time_value % 100:02}")
    print(f"End Time: {end_time_value // 100:02}:{end_time_value % 100:02}")
else:
    print("No solution found")