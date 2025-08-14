from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30

# Define the constraints for each participant
constraints = []

# Andrea is available all day
constraints.append(And(start_time >= 540, end_time <= 1020))  # 9:00 to 17:00 in minutes from 00:00

# Jack's constraints
jack_unavailable = [(540, 570), (840, 870)]  # 9:00-9:30, 14:00-14:30
for s, e in jack_unavailable:
    constraints.append(Or(end_time <= s, start_time >= e))

# Madison's constraints
madison_unavailable = [(570, 630), (780, 840), (900, 930), (990, 1050)]
for s, e in madison_unavailable:
    constraints.append(Or(end_time <= s, start_time >= e))

# Rachel's constraints
rachel_unavailable = [(570, 630), (660, 690), (720, 810), (870, 930), (960, 1020)]
for s, e in rachel_unavailable:
    constraints.append(Or(end_time <= s, start_time >= e))

# Douglas's constraints
douglas_unavailable = [(540, 690), (720, 990)]
for s, e in douglas_unavailable:
    constraints.append(Or(end_time <= s, start_time >= e))

# Ryan's constraints
ryan_unavailable = [(540, 570), (780, 840), (870, 1020)]
for s, e in ryan_unavailable:
    constraints.append(Or(end_time <= s, start_time >= e))

# Meeting duration constraint
constraints.append(end_time - start_time == meeting_duration)

# Create the solver
solver = Solver()

# Add all constraints to the solver
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[start_time].as_long()
    end_time_minutes = model[end_time].as_long()
    
    # Convert minutes back to HH:MM format
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found.")