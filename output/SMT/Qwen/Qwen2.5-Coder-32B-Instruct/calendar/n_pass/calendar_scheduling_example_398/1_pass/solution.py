from z3 import *

# Define the variables for the meeting time
day = "Monday"
start_time = Int('start_time')
end_time = start_time + 30  # Meeting duration is 30 minutes

# Define the constraints for each participant
constraints = [
    # Doris: 9:00 to 11:00, 13:30 to 14:00, 16:00 to 16:30
    Or(start_time >= 1100, end_time <= 900),
    Or(start_time >= 1400, end_time <= 1330),
    Or(start_time >= 1630, end_time <= 1600),

    # Theresa: 10:00 to 12:00
    Or(start_time >= 1200, end_time <= 1000),

    # Christian: No meetings the whole day
    # No constraints needed for Christian

    # Terry: 9:30 to 10:00, 11:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 14:30 to 15:00, 15:30 to 17:00
    Or(start_time >= 1000, end_time <= 930),
    Or(start_time >= 1200, end_time <= 1130),
    Or(start_time >= 1300, end_time <= 1230),
    Or(start_time >= 1400, end_time <= 1330),
    Or(start_time >= 1500, end_time <= 1430),
    Or(start_time >= 1700, end_time <= 1530),

    # Carolyn: 9:00 to 10:30, 11:00 to 11:30, 12:00 to 13:00, 13:30 to 14:30, 15:00 to 17:00
    Or(start_time >= 1030, end_time <= 900),
    Or(start_time >= 1130, end_time <= 1100),
    Or(start_time >= 1300, end_time <= 1200),
    Or(start_time >= 1430, end_time <= 1330),
    Or(start_time >= 1700, end_time <= 1500),

    # Kyle: 9:00 to 9:30, 11:30 to 12:00, 12:30 to 13:00, 14:30 to 17:00
    Or(start_time >= 930, end_time <= 900),
    Or(start_time >= 1200, end_time <= 1130),
    Or(start_time >= 1300, end_time <= 1230),
    Or(start_time >= 1700, end_time <= 1430),

    # General constraints: Meeting must be within working hours 9:00 to 17:00
    start_time >= 900,
    end_time <= 1700
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
    print(f"SOLUTION:\nDay: {day}\nStart Time: {start // 100:02}:{start % 100:02}\nEnd Time: {end // 100:02}:{end % 100:02}")
else:
    print("No solution found")