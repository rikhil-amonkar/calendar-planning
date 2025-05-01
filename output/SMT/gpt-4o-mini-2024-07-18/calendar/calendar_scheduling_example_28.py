from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
brittany_schedule = [
    (13 * 60, 13.5 * 60),  # 1:00 PM to 1:30 PM
    (16 * 60, 16.5 * 60)    # 4:00 PM to 4:30 PM
]
emily_schedule = []          # Emily is free all day
doris_schedule = [
    (9 * 60, 11 * 60),      # 9:00 AM to 11:00 AM
    (11.5 * 60, 14.5 * 60), # 11:30 AM to 2:30 PM
    (15 * 60, 17 * 60)      # 3:00 PM to 5:00 PM
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work ends

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for Brittany's and Doris's schedules
add_constraints(brittany_schedule, meeting_start)
add_constraints(doris_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")