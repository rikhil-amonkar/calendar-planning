from z3 import *

# Define the variables for the start time of the meeting
start_time = Int('start_time')

# Define the constraints for each participant
constraints = [
    # Gregory: not available from 9:00 to 9:30, 11:30 to 12:00
    Or(start_time >= 930, start_time < 900),
    Or(start_time >= 1200, start_time < 1130),
    
    # Jonathan: not available from 9:00 to 9:30, 12:00 to 12:30, 13:00 to 13:30, 15:00 to 16:00, 16:30 to 17:00
    Or(start_time >= 930, start_time < 900),
    Or(start_time >= 1230, start_time < 1200),
    Or(start_time >= 1330, start_time < 1300),
    Or(start_time >= 1600, start_time < 1500),
    Or(start_time >= 1700, start_time < 1630),
    
    # Barbara: not available from 10:00 to 10:30, 13:30 to 14:00
    Or(start_time >= 1030, start_time < 1000),
    Or(start_time >= 1400, start_time < 1330),
    
    # Jesse: not available from 10:00 to 11:00, 12:30 to 14:30
    Or(start_time >= 1100, start_time < 1000),
    Or(start_time >= 1430, start_time < 1230),
    
    # Alan: not available from 9:30 to 11:00, 11:30 to 12:30, 13:00 to 15:30, 16:00 to 17:00
    Or(start_time >= 1100, start_time < 930),
    Or(start_time >= 1230, start_time < 1130),
    Or(start_time >= 1530, start_time < 1300),
    Or(start_time >= 1700, start_time < 1600),
    
    # Nicole: not available from 9:00 to 10:30, 11:30 to 12:00, 12:30 to 13:30, 14:00 to 17:00
    Or(start_time >= 1030, start_time < 900),
    Or(start_time >= 1200, start_time < 1130),
    Or(start_time >= 1330, start_time < 1230),
    Or(start_time >= 1700, start_time < 1400),
    
    # Catherine: not available from 9:00 to 10:30, 12:00 to 13:30, 15:00 to 15:30, 16:00 to 16:30
    Or(start_time >= 1030, start_time < 900),
    Or(start_time >= 1330, start_time < 1200),
    Or(start_time >= 1530, start_time < 1500),
    Or(start_time >= 1630, start_time < 1600),
    
    # Meeting duration is 30 minutes, so the end time must be within working hours
    And(start_time >= 900, start_time + 30 <= 1700)
]

# Create a solver instance
solver = Solver()

# Add the constraints to the solver
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start // 100}:{start % 100:02d}")
    print(f"End Time: {(start + 30) // 100}:{(start + 30) % 100:02d}")
else:
    print("No solution found")