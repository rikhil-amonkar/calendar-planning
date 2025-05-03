from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
ralph_schedule = [
    (13.5 * 60, 14 * 60),  # 13:30 to 14:00
    (14.5 * 60, 15 * 60)   # 14:30 to 15:00
]
peter_schedule = [
    (9 * 60, 9.5 * 60),    # 9:00 to 9:30
    (11 * 60, 13 * 60),    # 11:00 to 13:00
    (16 * 60, 16.5 * 60)   # 16:00 to 16:30
]
daniel_schedule = [
    (9 * 60, 10 * 60),     # 9:00 to 10:00
    (10.5 * 60, 15.5 * 60),# 10:30 to 15:30
    (16 * 60, 17 * 60)     # 16:00 to 17:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Start time cannot be before work starts
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work ends

# Constraint for Daniel's preference to avoid meetings after 13:30
s.add(meeting_start + meeting_duration <= 13.5 * 60)  # Meeting must end by 13:30

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)  # Meeting must start after this participant's meeting ends

# Adding constraints for each participant's schedule
add_constraints(ralph_schedule, meeting_start)
add_constraints(peter_schedule, meeting_start)
add_constraints(daniel_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")