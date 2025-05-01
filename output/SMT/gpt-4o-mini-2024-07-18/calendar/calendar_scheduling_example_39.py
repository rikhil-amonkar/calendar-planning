from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
emily_schedule = []  # Emily is free all day
victoria_schedule = [
    (13.5 * 60, 14 * 60),  # 13:30 to 14:00
    (14.5 * 60, 15.5 * 60), # 14:30 to 15:30
    (16.5 * 60, 17 * 60)    # 16:30 to 17:00
]
nancy_schedule = [
    (9 * 60, 14 * 60),      # 9:00 to 14:00
    (14.5 * 60, 15.5 * 60)  # 14:30 to 15:30
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

# Adding constraints for Victoria's and Nancy's schedules
add_constraints(victoria_schedule, meeting_start)
add_constraints(nancy_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")