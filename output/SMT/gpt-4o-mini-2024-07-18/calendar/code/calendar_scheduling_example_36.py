from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Ryan": [
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
        (12 * 60 + 30, 13 * 60)     # 12:30 to 1:00
    ],
    "Ruth": [],                    # No busy times
    "Denise": [
        (9 * 60 + 30, 10 * 60 + 30), # 9:30 to 10:30
        (12 * 60, 13 * 60),          # 12:00 to 1:00
        (14 * 60 + 30, 16 * 60 + 30) # 2:30 to 4:30
    ]
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')

# Constraints: the meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints based on a participant's availability
def add_busy_constraints(participant):
    for busy_start, busy_end in busy_times[participant]:
        # Ensure meeting does not overlap with busy times
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add busy time constraints for all participants
for participant in busy_times:
    add_busy_constraints(participant)

# Add Denise's preference: avoid meetings after 12:30
solver.add(start_time <= (12 * 60 + 30))  # 12:30 in minutes

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")