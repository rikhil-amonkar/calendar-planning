from z3 import *

# Define the work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing busy times for James (in minutes from midnight)
james_busy = [(11 * 60 + 30, 12 * 60), (14 * 60 + 30, 15 * 60)]

# Define existing busy times for John (in minutes from midnight)
john_busy = [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60),
             (12 * 60 + 30, 13 * 60 + 30), (14 * 60 + 30, 16 * 60)]

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')

# Constraint: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Constraint: James' existing busy times
for busy_start, busy_end in james_busy:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Constraint: John's existing busy times
for busy_start, busy_end in john_busy:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")