from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Constants for the meeting duration
meeting_duration = 30  # 30 minutes

# Define the constraints
constraints = []

# Meeting must be between 9:00 and 17:00
constraints.append(start_time >= 9 * 60)
constraints.append(start_time + meeting_duration <= 17 * 60)

# Meeting must be on Monday (0) or Tuesday (1)
constraints.append(Or(day == 0, day == 1))

# Amanda's schedule
constraints.append(Implies(day == 0, Or(start_time >= 10 * 60 + 30, start_time < 9 * 60 + 30)))
constraints.append(Implies(day == 0, Or(start_time >= 11 * 60 + 30, start_time < 11 * 60)))
constraints.append(Implies(day == 0, Or(start_time >= 12 * 60 + 30, start_time < 12 * 60 + 30)))
constraints.append(Implies(day == 0, Or(start_time >= 14 * 60, start_time < 13 * 60)))
constraints.append(Implies(day == 0, Or(start_time >= 15 * 60, start_time < 14 * 60 + 30)))
constraints.append(Implies(day == 1, Or(start_time >= 9 * 60 + 30, start_time < 9 * 60)))
constraints.append(Implies(day == 1, Or(start_time >= 10 * 60 + 30, start_time < 10 * 60)))
constraints.append(Implies(day == 1, Or(start_time >= 12 * 60, start_time < 11 * 30)))
constraints.append(Implies(day == 1, Or(start_time >= 14 * 60 + 30, start_time < 13 * 30)))
constraints.append(Implies(day == 1, Or(start_time >= 16 * 60, start_time < 15 * 30)))
constraints.append(Implies(day == 1, Or(start_time >= 17 * 60, start_time < 16 * 30)))

# Nathan's schedule
constraints.append(Implies(day == 0, False))  # Nathan cannot meet on Monday
constraints.append(Implies(day == 1, Or(start_time >= 10 * 60 + 30, start_time < 9 * 60)))
constraints.append(Implies(day == 1, Or(start_time >= 13 * 60, start_time < 11 * 00)))
constraints.append(Implies(day == 1, Or(start_time >= 14 * 60, start_time < 13 * 30)))
constraints.append(Implies(day == 1, Or(start_time >= 15 * 60, start_time < 14 * 30)))
constraints.append(Implies(day == 1, Or(start_time >= 16 * 60, start_time < 15 * 30)))

# Amanda's preference: do not meet on Tuesday after 11:00
constraints.append(Implies(day == 1, start_time <= 11 * 60))

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time // 60:02}:{meeting_start_time % 60:02}")
    print(f"End Time: {meeting_end_time // 60:02}:{meeting_end_time % 60:02}")
else:
    print("No solution found")