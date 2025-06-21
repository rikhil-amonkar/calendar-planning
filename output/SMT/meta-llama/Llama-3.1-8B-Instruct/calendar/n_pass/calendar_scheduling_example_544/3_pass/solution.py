from z3 import *

# Define the variables
day = Int('day')
start_time = Real('start_time')
end_time = Real('end_time')
meeting_duration = Real('meeting_duration')

# Define the constraints
# Deborah is free the entire day
deborah_free = True

# Albert has blocked their calendar on Monday during 9:00 to 10:00, 10:30 to 12:00, 15:00 to 16:30
albert_blocked = Or(
    And(start_time >= 9, start_time < 10),
    And(start_time >= 10.5, start_time < 12),
    And(start_time >= 15, start_time < 16.5)
)

# Albert can not meet on Monday after 11:00
albert_after_11 = start_time < 11.5

# Meeting duration is half an hour
meeting_duration_val = 0.5
meeting_duration_constraint = Abs(start_time - end_time) == meeting_duration_val

# Meeting time should be between 9:00 to 17:00
meeting_time = And(start_time >= 9, start_time + meeting_duration_val < 17)

# Solve the constraints
solver = Solver()
solver.add([deborah_free, albert_blocked, albert_after_11, meeting_time, 
            meeting_duration_constraint, 
            day == 1,  # 1 represents Monday
            start_time >= 9,
            end_time <= 17])

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    print(f"SOLUTION:")
    print(f"Day: {model[day].as_long()}")
    print(f"Start Time: {model[start_time].numerator().as_long() / model[start_time].denominator().as_long():.2f}")
    print(f"End Time: {model[end_time].numerator().as_long() / model[end_time].denominator().as_long():.2f}")
else:
    print("No solution exists")