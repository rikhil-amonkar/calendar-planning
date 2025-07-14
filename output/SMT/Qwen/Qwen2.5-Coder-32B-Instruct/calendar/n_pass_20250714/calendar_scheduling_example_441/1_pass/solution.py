from z3 import *

# Define the variables for the meeting time
day = Int('day')  # Since the problem specifies Monday, we can assume day = 1 for simplicity
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 30

# Define the constraints for each participant
constraints = []

# Joan: 11:30 to 12:00, 14:30 to 15:00
constraints.append(Or(start_time >= 12 * 60, end_time <= 11 * 60 + 30))
constraints.append(Or(start_time >= 15 * 60, end_time <= 14 * 60 + 30))

# Megan: 9:00 to 10:00, 14:00 to 14:30, 16:00 to 16:30
constraints.append(Or(start_time >= 10 * 60, end_time <= 9 * 60))
constraints.append(Or(start_time >= 14 * 60 + 30, end_time <= 14 * 60))
constraints.append(Or(start_time >= 16 * 60 + 30, end_time <= 16 * 60))

# Austin: Free the entire day
# No constraints needed for Austin

# Betty: 9:30 to 10:00, 11:30 to 12:00, 13:30 to 14:00, 16:00 to 16:30
constraints.append(Or(start_time >= 10 * 60, end_time <= 9 * 60 + 30))
constraints.append(Or(start_time >= 12 * 60, end_time <= 11 * 60 + 30))
constraints.append(Or(start_time >= 14 * 60, end_time <= 13 * 60 + 30))
constraints.append(Or(start_time >= 16 * 60 + 30, end_time <= 16 * 60))

# Judith: 9:00 to 11:00, 12:00 to 13:00, 14:00 to 15:00
constraints.append(Or(start_time >= 11 * 60, end_time <= 9 * 60))
constraints.append(Or(start_time >= 13 * 60, end_time <= 12 * 60))
constraints.append(Or(start_time >= 15 * 60, end_time <= 14 * 60))

# Terry: 9:30 to 10:00, 11:30 to 12:30, 13:00 to 14:00, 15:00 to 15:30, 16:00 to 17:00
constraints.append(Or(start_time >= 10 * 60, end_time <= 9 * 60 + 30))
constraints.append(Or(start_time >= 12 * 60 + 30, end_time <= 11 * 60 + 30))
constraints.append(Or(start_time >= 14 * 60, end_time <= 13 * 60))
constraints.append(Or(start_time >= 15 * 60 + 30, end_time <= 15 * 60))
constraints.append(Or(start_time >= 17 * 60, end_time <= 16 * 60))

# Kathryn: 9:30 to 10:00, 10:30 to 11:00, 11:30 to 13:00, 14:00 to 16:00, 16:30 to 17:00
constraints.append(Or(start_time >= 10 * 60, end_time <= 9 * 60 + 30))
constraints.append(Or(start_time >= 11 * 60, end_time <= 10 * 60 + 30))
constraints.append(Or(start_time >= 13 * 60, end_time <= 11 * 60 + 30))
constraints.append(Or(start_time >= 16 * 60, end_time <= 14 * 60))
constraints.append(Or(start_time >= 17 * 60, end_time <= 16 * 60 + 30))

# General constraints: Meeting must be within 9:00 to 17:00 and last 30 minutes
constraints.append(start_time >= 9 * 60)
constraints.append(end_time <= 17 * 60)
constraints.append(end_time == start_time + meeting_duration)

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")