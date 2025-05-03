from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
andrew_schedule = []  # Andrew is free the entire day
grace_schedule = []    # Grace is free the entire day
samuel_schedule = [
    (9 * 60, 10.5 * 60),  # 9:00 to 10:30
    (11.5 * 60, 12 * 60), # 11:30 to 12:00
    (13 * 60, 13.5 * 60), # 1:00 to 1:30
    (14 * 60, 16 * 60),    # 2:00 to 4:00
    (16.5 * 60, 17 * 60)   # 4:30 to 5:00
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

# Adding constraints for Samuel's schedule
add_constraints(samuel_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")