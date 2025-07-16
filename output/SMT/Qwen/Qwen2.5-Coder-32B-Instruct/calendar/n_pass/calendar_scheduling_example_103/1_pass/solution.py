from z3 import *

# Define the variables for the meeting start time
start_time = Int('start_time')

# Define the constraints for the meeting duration (30 minutes) and work hours (9:00 to 17:00)
constraints = [
    start_time >= 9 * 60,          # Start time must be after or at 9:00
    start_time + 30 <= 17 * 60     # End time must be before or at 17:00
]

# Define the busy times for each participant
busy_times = {
    "Diane": [(9 * 60 + 30, 10 * 60), (14 * 60 + 30, 15 * 60)],
    "Jack": [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)],
    "Eugene": [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 14 * 60 + 30), (15 * 60, 16 * 60 + 30)],
    "Patricia": [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 12 * 60), (12 * 60 + 30, 14 * 60), (15 * 60, 16 * 60 + 30)]
}

# Add constraints to avoid busy times
for person, times in busy_times.items():
    for start, end in times:
        constraints.append(Or(start_time >= end, start_time + 30 <= start))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_start_hour = meeting_start // 60
    meeting_start_minute = meeting_start % 60
    meeting_end_hour = (meeting_start + 30) // 60
    meeting_end_minute = (meeting_start + 30) % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")