from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
grace_schedule = [
    (9 * 60, 9.5 * 60),   # 9:00 to 9:30
    (10 * 60, 11 * 60),   # 10:00 to 11:00
    (16 * 60, 16.5 * 60)  # 4:00 to 4:30
]
randy_schedule = [
    (12.5 * 60, 13 * 60), # 12:30 to 1:00
    (16 * 60, 16.5 * 60)  # 4:00 to 4:30
]
susan_schedule = [
    (9 * 60, 14.5 * 60),  # 9:00 to 2:30
    (15.5 * 60, 16 * 60)  # 3:30 to 4:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Start time cannot be before work starts
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work ends

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for Grace's, Randy's, and Susan's schedules
add_constraints(grace_schedule, meeting_start)
add_constraints(randy_schedule, meeting_start)
add_constraints(susan_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")