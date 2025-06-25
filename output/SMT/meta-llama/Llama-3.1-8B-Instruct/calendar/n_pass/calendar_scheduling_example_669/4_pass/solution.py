from z3 import *

# Define the variables
day = Int('day')
start_time = Real('start_time')
end_time = Real('end_time')

# Define the constraints
day_constraints = [day == 1]  # Try to schedule the meeting on Monday

start_time_constraints = [start_time >= 9, start_time < 11]  # Jean is busy on Tuesday during 11:30 to 12:00
start_time_constraints.append(start_time >= 11, start_time < 16)  # Jean is busy on Tuesday during 11:30 to 12:00
start_time_constraints.append(Or(start_time < 9, start_time >= 11))  # Jean is busy on Tuesday during 11:30 to 12:00
start_time_constraints.append(And(Not(start_time < 11), Not(start_time >= 16)))  # Jean is busy on Tuesday during 16:00 to 16:30
start_time_constraints.append(Or(start_time < 9, start_time >= 13.5))  # Doris is busy on Monday during 13:30 to 16:00
start_time_constraints.append(And(Or(start_time < 13.5, start_time >= 16.5)))  # Doris is busy on Monday during 16:30 to 17:00
start_time_constraints.append(Or(start_time < 9, start_time >= 9))  # Doris is busy on Tuesday during 9:00 to 17:00
start_time_constraints.append(start_time >= 14)  # Doris would rather not meet on Monday after 14:00

end_time_constraints = [end_time > start_time, end_time - start_time == 0.5]  # Meeting duration is half an hour

# Define the meeting duration
meeting_duration = 0.5

# Define the solver
solver = Solver()

# Add the constraints to the solver
solver.add(And(day_constraints))
solver.add(And(start_time >= 9, start_time <= 17))  # Meeting time is between 9:00 and 17:00
solver.add(And(start_time_constraints))
solver.add(And(end_time_constraints))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].numerator_as_long() / 3600
    end_time_value = model[end_time].numerator_as_long() / 3600

    # Print the solution
    print(f"SOLUTION:")
    print(f"Day: {'Monday' if day_value == 1 else 'Tuesday'}")
    print(f"Start Time: {int(start_time_value * 24):02d}:{int((start_time_value * 24 - int(start_time_value * 24)) * 60):02d}")
    print(f"End Time: {int(end_time_value * 24):02d}:{int((end_time_value * 24 - int(end_time_value * 24)) * 60):02d}")
else:
    print("No solution found")