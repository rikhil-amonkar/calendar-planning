from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
debra_schedule = [
    (9.5 * 60, 10 * 60),  # 9:30 to 10:00
    (11 * 60, 11.5 * 60), # 11:00 to 11:30
    (12 * 60, 13 * 60),   # 12:00 to 13:00
    (14 * 60, 14.5 * 60), # 14:00 to 14:30
    (16 * 60, 16.5 * 60)  # 16:00 to 16:30
]
kevin_schedule = [
    (9 * 60, 12 * 60),    # 9:00 to 12:00
    (14 * 60, 17 * 60)     # 14:00 to 17:00
]
# David has no meetings, so no constraints need to be added for him

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

# Adding constraints for Debra and Kevin's schedules
add_constraints(debra_schedule, meeting_start)
add_constraints(kevin_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")