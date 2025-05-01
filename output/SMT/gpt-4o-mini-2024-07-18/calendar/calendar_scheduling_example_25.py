from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
anthony_schedule = [
    (9.5 * 60, 10 * 60),   # 9:30 to 10:00
    (12 * 60, 13 * 60),    # 12:00 to 13:00
    (16 * 60, 16.5 * 60)   # 16:00 to 16:30
]
pamela_schedule = [
    (9.5 * 60, 10 * 60),   # 9:30 to 10:00
    (16.5 * 60, 17 * 60)    # 16:30 to 17:00
]
zachary_schedule = [
    (9 * 60, 11.5 * 60),   # 9:00 to 11:30
    (12 * 60, 12.5 * 60),  # 12:00 to 12:30
    (13 * 60, 13.5 * 60),  # 13:00 to 13:30
    (14.5 * 60, 15 * 60),   # 14:30 to 15:00
    (16 * 60, 17 * 60)      # 16:00 to 17:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Start time cannot be before work starts
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work ends

# Constraint for Pamela's preference to avoid meetings after 14:30
s.add(meeting_start + meeting_duration <= 14.5 * 60)  # Meeting must end by 14:30

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for Anthony's, Pamela's, and Zachary's schedules
add_constraints(anthony_schedule, meeting_start)
add_constraints(pamela_schedule, meeting_start)
add_constraints(zachary_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")