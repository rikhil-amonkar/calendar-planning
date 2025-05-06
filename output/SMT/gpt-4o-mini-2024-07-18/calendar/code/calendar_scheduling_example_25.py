from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing busy times for Anthony (in minutes from midnight)
anthony_busy = [
    (9 * 60 + 30, 10 * 60),  # 9:30 - 10:00
    (12 * 60, 13 * 60),      # 12:00 - 1:00
    (16 * 60, 16 * 60 + 30)  # 4:00 - 4:30
]

# Define existing busy times for Pamela (in minutes from midnight)
pamela_busy = [
    (9 * 60 + 30, 10 * 60),  # 9:30 - 10:00
    (16 * 60 + 30, 17 * 60)   # 4:30 - 5:00
]

# Define existing busy times for Zachary (in minutes from midnight)
zachary_busy = [
    (9 * 60, 11 * 60 + 30),  # 9:00 - 11:30
    (12 * 60, 12 * 60 + 30),  # 12:00 - 12:30
    (13 * 60, 13 * 60 + 30),  # 1:00 - 1:30
    (14 * 60 + 30, 15 * 60),  # 2:30 - 3:00
    (16 * 60, 17 * 60)        # 4:00 - 5:00
]

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints
def add_busy_constraints(busy_times):
    for busy_start, busy_end in busy_times:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add busy constraints for Anthony, Pamela, and Zachary
add_busy_constraints(anthony_busy)
add_busy_constraints(pamela_busy)
add_busy_constraints(zachary_busy)

# Add constraint for Pamela: avoid meetings after 14:30 (2:30 PM)
solver.add(start_time <= (14 * 60 + 30 - meeting_duration))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")