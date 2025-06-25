from z3 import *

# Define the variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

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
meeting_duration = 0.5

# Meeting time should be between 9:00 to 17:00
meeting_time = And(start_time >= 9, start_time < 17)

# Solve the constraints
solver = Solver()
solver.add([deborah_free, albert_blocked, albert_after_11, meeting_time, 
            start_time + meeting_duration == end_time, 
            day == 1])  # 1 represents Monday

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    print(f"SOLUTION:")
    print(f"Day: {model[day].as_long()}")
    print(f"Start Time: {model[start_time].as_real().as_decimal(2)}")
    print(f"End Time: {model[end_time].as_real().as_decimal(2)}")
else:
    print("No solution exists")