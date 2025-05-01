from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
benjamin_schedule = []  # Benjamin is free all day
hannah_schedule = []    # Hannah is free all day
brenda_schedule = [
    (9.5 * 60, 10 * 60),   # 9:30 to 10:00
    (11.5 * 60, 12.5 * 60),# 11:30 to 12:30
    (14 * 60, 16.5 * 60)   # 14:00 to 16:30
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Start time cannot be before work starts
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work ends

# Constraint for Benjamin's preference to avoid meetings after 9:30
s.add(meeting_start + meeting_duration <= 9.5 * 60)  # Meeting must end by 9:30

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                       # Meeting must start after this participant's meeting ends

# Adding constraints for Brenda's schedule
add_constraints(brenda_schedule, meeting_start)
# No constraints for Benjamin or Hannah since they are free all day

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")