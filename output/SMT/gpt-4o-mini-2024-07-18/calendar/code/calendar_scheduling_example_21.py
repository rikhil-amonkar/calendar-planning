from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
scott_schedule = [
    (11.5 * 60, 12 * 60),  # 11:30 to 12:00
    (15.5 * 60, 16 * 60)   # 15:30 to 16:00
]
kimberly_schedule = [
    (11 * 60, 12 * 60),    # 11:00 to 12:00
    (12.5 * 60, 13 * 60),  # 12:30 to 13:00
    (13.5 * 60, 14 * 60),  # 13:30 to 14:00
    (14.5 * 60, 15 * 60),  # 14:30 to 15:00
    (15.5 * 60, 17 * 60)   # 15:30 to 17:00
]
# Bobby has no meetings, so we do not need to add any constraints for him.

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
        s.add(meeting_start >= end)  # Meeting must start after this participant's meeting ends

# Adding constraints for Scott's and Kimberly's schedules
add_constraints(scott_schedule, meeting_start)
add_constraints(kimberly_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")