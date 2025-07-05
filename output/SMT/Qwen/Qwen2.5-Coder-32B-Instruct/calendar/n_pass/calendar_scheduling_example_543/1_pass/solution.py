from z3 import *

# Define the variables for the meeting start time in minutes since the start of the day (9:00)
meeting_start = Int('meeting_start')
meeting_duration = 60  # Meeting duration is 1 hour

# Define the constraints for the available time slots
# Work hours are from 9:00 to 17:00, which is 480 to 1020 minutes since the start of the day
work_start = 480
work_end = 1020

# Define the constraints for James and John
james_busy_slots = [(750, 780), (870, 900)]  # 11:30 to 12:00, 14:30 to 15:00 in minutes
john_busy_slots = [(570, 660), (750, 780), (780, 810), (870, 990)]  # 9:30 to 11:00, 11:30 to 12:00, 12:30 to 13:30, 14:30 to 16:30 in minutes

# Create the solver
solver = Solver()

# Add constraints for the meeting to be within work hours
solver.add(meeting_start >= work_start)
solver.add(meeting_start + meeting_duration <= work_end)

# Add constraints to avoid busy slots for James
for start, end in james_busy_slots:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Add constraints to avoid busy slots for John
for start, end in john_busy_slots:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{9 + meeting_start_minutes // 60}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{9 + (meeting_start_minutes + meeting_duration) // 60}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")