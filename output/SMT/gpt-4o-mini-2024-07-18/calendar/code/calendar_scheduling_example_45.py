from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Andrew": [],  # Andrew is wide open all day
    "Grace": [],   # Grace has no meetings all day
    "Samuel": [
        (9 * 60, 10 * 60 + 30),    # 9:00 to 10:30
        (11 * 60 + 30, 12 * 60),   # 11:30 to 12:00
        (13 * 60, 13 * 60 + 30),   # 13:00 to 13:30
        (14 * 60, 16 * 60),         # 14:00 to 16:00
        (16 * 60 + 30, 17 * 60)     # 16:30 to 17:00
    ]
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for each participant
def add_busy_constraints(participant):
    for busy_start, busy_end in busy_times[participant]:
        # Ensure the meeting does not overlap with busy times
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add busy time constraints for Samuel since Andrew and Grace are free
add_busy_constraints("Samuel")

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")