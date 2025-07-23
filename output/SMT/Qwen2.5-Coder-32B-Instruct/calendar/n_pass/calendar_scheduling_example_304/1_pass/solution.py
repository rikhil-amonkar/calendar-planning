from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the time variable
time = Int('time')

# Define the constraints for each participant
constraints = [
    # Christine is busy on Monday during 9:30 to 10:30, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:00, 16:00 to 16:30
    Or(time < 9*60 + 30, time >= 10*60 + 30),
    Or(time < 12*60, time >= 12*60 + 30),
    Or(time < 13*60, time >= 13*60 + 30),
    Or(time < 14*60 + 30, time >= 15*60),
    Or(time < 16*60, time >= 16*60 + 30),

    # Bobby is busy on Monday during 12:00 to 12:30, 14:30 to 15:00
    Or(time < 12*60, time >= 12*60 + 30),
    Or(time < 14*60 + 30, time >= 15*60),

    # Elizabeth is busy on Monday during 9:00 to 9:30, 11:30 to 13:00, 13:30 to 14:00, 15:00 to 15:30, 16:00 to 17:00
    Or(time < 9*60, time >= 9*60 + 30),
    Or(time < 11*60 + 30, time >= 13*60),
    Or(time < 13*60 + 30, time >= 14*60),
    Or(time < 15*60, time >= 15*60 + 30),
    Or(time < 16*60, time >= 17*60),

    # Tyler is busy on Monday during 9:00 to 11:00, 12:00 to 12:30, 13:00 to 13:30, 15:30 to 16:00, 16:30 to 17:00
    Or(time < 9*60, time >= 11*60),
    Or(time < 12*60, time >= 12*60 + 30),
    Or(time < 13*60, time >= 13*60 + 30),
    Or(time < 15*60 + 30, time >= 16*60),
    Or(time < 16*60 + 30, time >= 17*60),

    # Edward is busy on Monday during 9:00 to 9:30, 10:00 to 11:00, 11:30 to 14:00, 14:30 to 15:30, 16:00 to 17:00
    Or(time < 9*60, time >= 9*60 + 30),
    Or(time < 10*60, time >= 11*60),
    Or(time < 11*60 + 30, time >= 14*60),
    Or(time < 14*60 + 30, time >= 15*60 + 30),
    Or(time < 16*60, time >= 17*60),

    # Janice would rather not meet on Monday after 13:00
    time < 13*60
]

# Define the solver
solver = Solver()

# Add constraints to the solver
solver.add(constraints)

# Add the constraint that the meeting must start within the work hours and fit the duration
solver.add(time >= start_time)
solver.add(time + meeting_duration <= end_time)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start // 60}:{meeting_start % 60:02}")
    print(f"End Time: {meeting_end // 60}:{meeting_end % 60:02}")
else:
    print("No solution found")