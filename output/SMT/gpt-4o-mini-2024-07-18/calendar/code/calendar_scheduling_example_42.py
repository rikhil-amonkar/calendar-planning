from z3 import *

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing busy times for each participant (in minutes from midnight)
busy_times = {
    "Julie": [
        (9 * 60, 9 * 60 + 30),  # 9:00 - 9:30
        (11 * 60, 11 * 60 + 30), # 11:00 - 11:30
        (12 * 60, 12 * 60 + 30), # 12:00 - 12:30
        (13 * 60 + 30, 14 * 60), # 1:30 - 2:00
        (16 * 60, 17 * 60)       # 4:00 - 5:00
    ],
    "Sean": [
        (9 * 60, 9 * 60 + 30),   # 9:00 - 9:30
        (13 * 60, 13 * 60 + 30), # 1:00 - 1:30
        (15 * 60, 15 * 60 + 30), # 3:00 - 3:30
        (16 * 60, 16 * 60 + 30)  # 4:00 - 4:30
    ],
    "Lori": [
        (10 * 60, 10 * 60 + 30), # 10:00 - 10:30
        (11 * 60, 13 * 60),       # 11:00 - 1:00
        (15 * 60 + 30, 17 * 60)   # 3:30 - 5:00
    ]
}

# Initialize the Z3 solver
solver = Solver()

# Variable for the start time of the meeting
start_time = Int('start_time')

# Constraints: meeting must occur during work hours
solver.add(start_time >= work_start)
solver.add(start_time + meeting_duration <= work_end)

# Function to add busy time constraints for each participant
def add_busy_constraints(busy_times):
    for participant_times in busy_times.values():
        for busy_start, busy_end in participant_times:
            solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Add busy time constraints for all participants
add_busy_constraints(busy_times)

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print(f"Meeting can be scheduled from {meeting_start // 60:02}:{meeting_start % 60:02} to {meeting_end // 60:02}:{meeting_end % 60:02}")
else:
    print("No available time found for the meeting.")