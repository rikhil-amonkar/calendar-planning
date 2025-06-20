from z3 import *

# Define the day of the week (Monday is 0)
day = Int('day')
day_val = If(day == 0, 'Monday', 'Tuesday')

# Define the start and end time of the meeting
start_time = Int('start_time')
end_time = start_time + 30

# Define the constraints for Randy's schedule
randy_blocked = [
    (start_time >= 9, start_time < 10.5),
    (start_time >= 11, start_time < 15.5),
    (start_time >= 16, start_time < 17)
]

# Define the constraint for Evelyn's preference
evelyn_preference = start_time < 13

# Define the meeting duration
meeting_duration = 30

# Define the solver
solver = Solver()

# Add the constraints to the solver
for constraint in randy_blocked:
    solver.add(Or(*constraint))
solver.add(evelyn_preference)

# Check if there is a solution
if solver.check() == sat:
    # Get the model
    model = solver.model()
    # Extract the values from the model
    day_val = model[day].as_string()
    start_time_val = model[start_time].as_real().numerator / 60
    # Print the solution
    print(f"SOLUTION:")
    print(f"Day: {day_val}")
    print(f"Start Time: {int(start_time_val):02d}:00")
    print(f"End Time: {(int(start_time_val) + int(meeting_duration)):02d}:30")
else:
    print("No solution found")