from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing busy times for Nicole (in minutes from midnight)
nicole_busy = [
    (9 * 60, 10 * 60),    # 9:00 - 10:00
    (10 * 60 + 30, 16 * 60 + 30)  # 10:30 - 4:30
]

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for Nicole
def add_busy_constraints(busy_times):
    for busy_start, busy_end in busy_times:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add busy constraints for Nicole
add_busy_constraints(nicole_busy)

# Add constraint for Nicole: avoid meeting before 16:00 (4:00 PM)
solver.add(start_time >= (16 * 60))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")