from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing busy times for Albert (in minutes from midnight)
albert_busy = [
    (9 * 60, 10 * 60),    # 9:00 - 10:00
    (10 * 60 + 30, 12 * 60),  # 10:30 - 12:00
    (15 * 60, 16 * 60 + 30)  # 15:00 - 16:30
]

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')

# Constraint: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Constraint: Albert's existing busy times
for busy_start, busy_end in albert_busy:
    solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Additional constraint: Albert cannot meet after 11:00 (11:00 AM in minutes)
max_meeting_start_after_11 = 11 * 60 - meeting_duration
solver.add(start_time <= max_meeting_start_after_11)

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")