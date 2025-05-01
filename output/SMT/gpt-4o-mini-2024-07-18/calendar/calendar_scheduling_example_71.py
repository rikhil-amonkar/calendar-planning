from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
nicole_schedule = []  # Nicole is free all day
john_schedule = [
    (12.5 * 60, 13 * 60),  # 12:30 to 1:00
    (16.5 * 60, 17 * 60)    # 4:30 to 5:00
]
ethan_schedule = [
    (9 * 60, 10 * 60),      # 9:00 to 10:00
    (11.5 * 60, 14 * 60),   # 11:30 to 2:00
    (14.5 * 60, 17 * 60)    # 2:30 to 5:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Constraint for John's preference to avoid meetings after 12:00
s.add(meeting_start + meeting_duration <= 12 * 60)  # Meeting must end by noon (12:00)

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for John's and Ethan's schedules
add_constraints(john_schedule, meeting_start)
add_constraints(ethan_schedule, meeting_start)
# No constraints needed for Nicole since she is available all day

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")