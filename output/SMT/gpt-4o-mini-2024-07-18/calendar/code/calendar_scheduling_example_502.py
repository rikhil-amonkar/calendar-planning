from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing busy times for Jack (in minutes from midnight)
jack_busy = [
    (9 * 60 + 30, 10 * 60 + 30),  # 9:30 - 10:30
    (11 * 60, 11 * 60 + 30),       # 11:00 - 11:30
    (12 * 60 + 30, 13 * 60),       # 12:30 - 1:00
    (14 * 60, 14 * 60 + 30),       # 2:00 - 2:30
    (16 * 60, 16 * 60 + 30)        # 4:00 - 4:30
]

# Define existing busy times for Charlotte (in minutes from midnight)
charlotte_busy = [
    (9 * 60 + 30, 10 * 60),        # 9:30 - 10:00
    (10 * 60 + 30, 12 * 60),       # 10:30 - 12:00
    (12 * 60 + 30, 13 * 60 + 30),  # 12:30 - 1:30
    (14 * 60, 16 * 60)             # 2:00 - 4:00
]

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for Jack
def add_jack_constraints():
    for busy_start, busy_end in jack_busy:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Function to add busy time constraints for Charlotte
def add_charlotte_constraints():
    for busy_start, busy_end in charlotte_busy:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add busy constraints for Jack and Charlotte
add_jack_constraints()
add_charlotte_constraints()

# Add constraint for Jack: avoid meetings after 12:30
solver.add(start_time <= (12 * 60 + 30 - meeting_duration))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")