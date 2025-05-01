from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
brandon_schedule = [
    (13 * 60, 14 * 60),  # 13:00 to 14:00
    (15.5 * 60, 16 * 60), # 15:30 to 16:00
    (16.5 * 60, 17 * 60)  # 16:30 to 17:00
]
jerry_schedule = []  # Jerry has no meetings, so no constraints need to be added for him
bradley_schedule = [
    (9 * 60, 11.5 * 60),  # 9:00 to 11:30
    (12 * 60, 15 * 60),    # 12:00 to 15:00
    (16 * 60, 16.5 * 60)   # 16:00 to 16:30
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Start time cannot be before work starts
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work ends

# Constraint for Brandon's preference to avoid meetings before 14:30
s.add(meeting_start >= 14.5 * 60)  # Meeting cannot start before 14:30

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)  # Meeting must start after this participant's meeting ends

# Adding constraints for Brandon's and Bradley's schedules
add_constraints(brandon_schedule, meeting_start)
add_constraints(bradley_schedule, meeting_start)
# No constraints added for Jerry since he has no meetings.

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")