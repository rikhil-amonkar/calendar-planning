from z3 import *

# Define the time slots from 9:00 to 17:00 in 30-minute increments
time_slots = [900 + 30*i for i in range(16)]  # This gives us times from 900 (9:00) to 1630 (16:30)

# Create a variable to represent the start time of the meeting
start_time = Int('start_time')

# Constraints for each participant
constraints = [
    # Emily: 10:00 to 10:30, 16:00 to 16:30
    Or(start_time < 1000, start_time >= 1030),
    Or(start_time < 1600, start_time >= 1630),

    # Mason: Free all day
    True,

    # Maria: 10:30 to 11:00, 14:00 to 14:30
    Or(start_time < 1030, start_time >= 1100),
    Or(start_time < 1400, start_time >= 1430),

    # Carl: 9:30 to 10:00, 10:30 to 12:30, 13:30 to 14:00, 14:30 to 15:30, 16:00 to 17:00
    Or(start_time < 930, start_time >= 1000),
    Or(start_time < 1030, start_time >= 1230),
    Or(start_time < 1330, start_time >= 1400),
    Or(start_time < 1430, start_time >= 1530),
    Or(start_time < 1600, start_time >= 1700),

    # David: 9:30 to 11:00, 11:30 to 12:00, 12:30 to 13:30, 14:00 to 15:00, 16:00 to 17:00
    Or(start_time < 930, start_time >= 1100),
    Or(start_time < 1130, start_time >= 1200),
    Or(start_time < 1230, start_time >= 1330),
    Or(start_time < 1400, start_time >= 1500),
    Or(start_time < 1600, start_time >= 1700),

    # Frank: 9:30 to 10:30, 11:00 to 11:30, 12:30 to 13:30, 14:30 to 17:00
    Or(start_time < 930, start_time >= 1030),
    Or(start_time < 1100, start_time >= 1130),
    Or(start_time < 1230, start_time >= 1330),
    Or(start_time < 1430, start_time >= 1700),

    # Meeting duration is 30 minutes
    And(start_time >= 900, start_time <= 1630)
]

# Create a solver instance
solver = Solver()

# Add all constraints to the solver
for constraint in constraints:
    solver.add(constraint)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start = model[start_time].as_long()
    end = start + 30

    # Format the time in HH:MM format
    start_time_formatted = f"{start // 100:02}:{start % 100:02}"
    end_time_formatted = f"{end // 100:02}:{end % 100:02}"

    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time_formatted}")
    print(f"End Time: {end_time_formatted}")
else:
    print("No solution found")