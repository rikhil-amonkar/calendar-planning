from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
alexander_schedule = [
    (9.5 * 60, 10 * 60),  # 9:30 to 10:00
    (10.5 * 60, 11 * 60), # 10:30 to 11:00
    (12.5 * 60, 13 * 60), # 12:30 to 13:00
    (14.5 * 60, 15 * 60), # 14:30 to 15:00
    (16 * 60, 17 * 60)    # 16:00 to 17:00
]
elizabeth_schedule = [
    (9 * 60, 9.5 * 60),   # 9:00 to 9:30
    (11.5 * 60, 12.5 * 60), # 11:30 to 12:30
    (13 * 60, 14.5 * 60)  # 13:00 to 14:30
]
walter_schedule = [
    (9 * 60, 14.5 * 60),  # 9:00 to 14:30
    (15.5 * 60, 17 * 60)  # 15:30 to 17:00
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
        s.add(meeting_start >= end)  # Meeting must start after this participant's meeting ends

# Adding constraints for each participant's schedule
add_constraints(alexander_schedule, meeting_start)
add_constraints(elizabeth_schedule, meeting_start)
add_constraints(walter_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")