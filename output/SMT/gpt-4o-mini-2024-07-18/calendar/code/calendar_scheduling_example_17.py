from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define busy times for each participant (in minutes from midnight)
busy_times = {
    "Margaret": [
        (9 * 60, 10 * 60),        # 9:00 to 10:00
        (10 * 60 + 30, 11 * 60),  # 10:30 to 11:00
        (11 * 60 + 30, 12 * 60),  # 11:30 to 12:00
        (13 * 60, 13 * 60 + 30),  # 1:00 to 1:30
        (15 * 60, 15 * 60 + 30)   # 3:00 to 3:30
    ],
    "Donna": [
        (14 * 60 + 30, 15 * 60),  # 2:30 to 3:00
        (16 * 60, 16 * 60 + 30)    # 4:00 to 4:30
    ],
    "Helen": [
        (9 * 60, 9 * 60 + 30),    # 9:00 to 9:30
        (10 * 60, 11 * 60 + 30),  # 10:00 to 11:30
        (13 * 60, 14 * 60),       # 1:00 to 2:00
        (14 * 60 + 30, 15 * 60),  # 2:30 to 3:00
        (15 * 60 + 30, 17 * 60)   # 3:30 to 5:00
    ]
}

# Initialize Z3 Solver
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

# Add busy time constraints for all participants
add_busy_constraints("Margaret")
add_busy_constraints("Donna")
add_busy_constraints("Helen")

# Add Helen's preference: cannot meet after 13:30
solver.add(start_time <= (13 * 60 + 30))  # 13:30 in minutes

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")