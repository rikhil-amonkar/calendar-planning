from z3 import *

# Define the variables for the meeting time
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

# Define the constraints for the meeting duration
meeting_duration = 60  # 1 hour meeting

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes from 00:00
work_end = 17 * 60   # 17:00 in minutes from 00:00

# Define Kayla's blocked times in minutes from 00:00
kayla_blocked_times = [
    (10 * 60, 10 * 60 + 30),  # 10:00 to 10:30
    (14 * 60 + 30, 16 * 60)   # 14:30 to 16:00
]

# Define Rebecca's blocked times in minutes from 00:00
rebecca_blocked_times = [
    (9 * 60, 13 * 60),        # 9:00 to 13:00
    (13 * 60 + 30, 15 * 60),  # 13:30 to 15:00
    (15 * 60 + 30, 16 * 60)   # 15:30 to 16:00
]

# Create a solver instance
solver = Solver()

# Add constraints for the meeting time to be within work hours
solver.add(meeting_start >= work_start)
solver.add(meeting_end <= work_end)

# Add constraint for the meeting duration
solver.add(meeting_end == meeting_start + meeting_duration)

# Add constraints to avoid Kayla's blocked times
for start, end in kayla_blocked_times:
    solver.add(Or(meeting_end <= start, meeting_start >= end))

# Add constraints to avoid Rebecca's blocked times
for start, end in rebecca_blocked_times:
    solver.add(Or(meeting_end <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_end_minutes = model[meeting_end].as_long()
    
    # Convert minutes back to HH:MM format
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{meeting_end_minutes // 60:02}:{meeting_end_minutes % 60:02}"
    
    # Print the solution
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_time}")
    print(f"End Time: {meeting_end_time}")
else:
    print("No solution found.")