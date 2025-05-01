from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
samuel_schedule = [
    (9 * 60, 9.5 * 60),   # 9:00 to 9:30
    (10 * 60, 10.5 * 60), # 10:00 to 10:30
    (12 * 60, 12.5 * 60), # 12:00 to 12:30
    (14 * 60, 15 * 60),   # 14:00 to 15:00
    (16 * 60, 16.5 * 60)  # 16:00 to 16:30
]
emma_schedule = []       # Emma is free all day
brittany_schedule = [
    (11.5 * 60, 14.5 * 60), # 11:30 to 14:30
    (15 * 60, 15.5 * 60),    # 15:00 to 15:30
    (16.5 * 60, 17 * 60)     # 16:30 to 17:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for Samuel's and Brittany's schedules
add_constraints(samuel_schedule, meeting_start)
add_constraints(brittany_schedule, meeting_start)
# No constraints for Emma since she is available all day.

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")