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
    Or(meeting_start >= 10 * 60, meeting_end <= 9 * 60),  # 9:00 to 10:00
    Or(meeting_start >= 11 * 00, meeting_end <= 10 * 30),  # 10:30 to 11:00
    Or(meeting_start >= 14 * 30, meeting_end <= 14 * 30),  # 14:30 to 15:00
    Or(meeting_start >= 15 * 30, meeting_end <= 15 * 30),  # 15:30 to 16:00
    Or(meeting_start >= 16 * 30, meeting_end <= 16 * 30),  # 16:30 to 17:00
    
    # Bruce's availability
    Or(meeting_start >= 11 * 30, meeting_end <= 11 * 00),  # 11:00 to 11:30
    Or(meeting_start >= 13 * 00, meeting_end <= 12 * 30),  # 12:30 to 13:00
    Or(meeting_start >= 14 * 30, meeting_end <= 14 * 00),  # 14:00 to 14:30
    Or(meeting_start >= 16 * 00, meeting_end <= 15 * 30),  # 15:30 to 16:00
    
    # Eric's availability
    Or(meeting_start >= 9 * 30, meeting_end <= 9 * 00),    # 9:00 to 9:30
    Or(meeting_start >= 11 * 00, meeting_end <= 10 * 00),  # 10:00 to 11:00
    Or(meeting_start >= 13 * 00, meeting_end <= 11 * 30),  # 11:30 to 13:00
    Or(meeting_start >= 15 * 30, meeting_end <= 14 * 30),  # 14:30 to 15:30
]

# Add additional constraints to avoid specific conflicts
constraints.append(Or(meeting_start >= 11 * 00, meeting_end <= 10 * 30))  # Avoid 10:30 to 11:00

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