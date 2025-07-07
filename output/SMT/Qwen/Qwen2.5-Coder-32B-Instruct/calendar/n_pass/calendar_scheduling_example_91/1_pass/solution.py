from z3 import *

# Define the variables for the meeting time
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

# Define the constraints
constraints = [
    # Meeting must be within work hours (9:00 to 17:00)
    meeting_start >= 9 * 60,
    meeting_end <= 17 * 60,
    # Meeting duration is 1 hour
    meeting_end == meeting_start + 60,
    
    # Danielle's availability
    Or(meeting_start >= 10 * 60, meeting_end <= 10 * 60),
    Or(meeting_start >= 11 * 60, meeting_end <= 10 * 30),
    Or(meeting_start >= 14 * 30, meeting_end <= 14 * 30),
    Or(meeting_start >= 15 * 30, meeting_end <= 15 * 30),
    Or(meeting_start >= 16 * 30, meeting_end <= 16 * 30),
    
    # Bruce's availability
    Or(meeting_start >= 11 * 30, meeting_end <= 11 * 00),
    Or(meeting_start >= 13 * 00, meeting_end <= 12 * 30),
    Or(meeting_start >= 14 * 30, meeting_end <= 14 * 00),
    Or(meeting_start >= 16 * 00, meeting_end <= 15 * 30),
    
    # Eric's availability
    Or(meeting_start >= 9 * 30, meeting_end <= 9 * 00),
    Or(meeting_start >= 11 * 00, meeting_end <= 10 * 00),
    Or(meeting_start >= 13 * 00, meeting_end <= 11 * 30),
    Or(meeting_start >= 15 * 30, meeting_end <= 14 * 30),
]

# Create a solver instance
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[meeting_start].as_long()
    end_time_minutes = model[meeting_end].as_long()
    start_hour, start_minute = divmod(start_time_minutes, 60)
    end_hour, end_minute = divmod(end_time_minutes, 60)
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")