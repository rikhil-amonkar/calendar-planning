from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
virginia_schedule = [
    (10 * 60, 12 * 60),   # 10:00 to 12:00
]
charles_schedule = [
    (12 * 60, 12.5 * 60), # 12:00 to 12:30
    (13 * 60, 13.5 * 60),  # 1:00 to 1:30
]
megan_schedule = [
    (9 * 60, 12 * 60),     # 9:00 to 12:00
    (13.5 * 60, 16 * 60),  # 1:30 to 4:00
    (16.5 * 60, 17 * 60)    # 4:30 to 5:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Constraint for Charles's preference to avoid meetings after 14:30
s.add(meeting_start + meeting_duration <= 14.5 * 60)  # Meeting must end by 14:30

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for Virginia's, Charles's, and Megan's schedules
add_constraints(virginia_schedule, meeting_start)
add_constraints(charles_schedule, meeting_start)
add_constraints(megan_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")