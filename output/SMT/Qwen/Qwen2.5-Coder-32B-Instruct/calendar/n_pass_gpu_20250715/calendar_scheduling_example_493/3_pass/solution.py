from z3 import *

# Define the variables
day = "Monday"
start_time = Int('start_time')
end_time = Int('end_time')
meeting_duration = 30  # in minutes

# Define the constraints for each participant
constraints = []

# Tyler is free the entire day
constraints.append(And(start_time >= 9*60, end_time <= 17*60))

# Kelly has no meetings the whole day
constraints.append(And(start_time >= 9*60, end_time <= 17*60))

# Stephanie has blocked their calendar on Monday during 11:00 to 11:30, 14:30 to 15:00
constraints.append(Or(end_time <= 11*60, start_time >= 11*60 + 30,
                     end_time <= 14*60 + 30, start_time >= 15*60))

# Hannah has no meetings the whole day
constraints.append(And(start_time >= 9*60, end_time <= 17*60))

# Joe has blocked their calendar on Monday during 9:00 to 9:30, 10:00 to 12:00, 12:30 to 13:00, 14:00 to 17:00
constraints.append(Or(end_time <= 9*60 + 30, start_time >= 9*60,
                     end_time <= 12*60, start_time >= 12*60,
                     end_time <= 13*60, start_time >= 12*60 + 30,
                     end_time <= 14*60, start_time >= 17*60))

# Diana has meetings on Monday during 9:00 to 10:30, 11:30 to 12:00, 13:00 to 14:00, 14:30 to 15:30, 16:00 to 17:00
constraints.append(Or(end_time <= 10*60 + 30, start_time >= 9*60,
                     end_time <= 12*60, start_time >= 11*60 + 30,
                     end_time <= 14*60, start_time >= 13*60,
                     end_time <= 15*60 + 30, start_time >= 14*60 + 30,
                     end_time <= 17*60, start_time >= 16*60))

# Deborah is busy on Monday during 9:00 to 10:00, 10:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 14:30 to 15:30, 16:00 to 16:30
constraints.append(Or(end_time <= 10*60, start_time >= 9*60,
                     end_time <= 12*60, start_time >= 10*60 + 30,
                     end_time <= 13*60, start_time >= 12*60 + 30,
                     end_time <= 14*60, start_time >= 13*60 + 30,
                     end_time <= 15*60 + 30, start_time >= 14*60 + 30,
                     end_time <= 16*60 + 30, start_time >= 16*60))

# Add the constraint that the meeting duration is 30 minutes
constraints.append(end_time == start_time + meeting_duration)

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = model[end_time].as_long()
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start // 60}:{start % 60:02}")
    print(f"End Time: {end // 60}:{end % 60:02}")
else:
    print("No solution found")