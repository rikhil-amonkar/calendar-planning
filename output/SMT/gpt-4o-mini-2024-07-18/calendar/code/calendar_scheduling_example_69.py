from z3 import *

# Define working hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
shirley_schedule = [
    (11 * 60, 11.5 * 60),  # 11:00 to 11:30
    (14 * 60, 15 * 60),     # 14:00 to 15:00
    (16 * 60, 16.5 * 60)    # 16:00 to 16:30
]
stephen_schedule = [
    (13 * 60, 13.5 * 60),   # 13:00 to 13:30
    (15.5 * 60, 16 * 60)    # 15:30 to 16:00
]
paul_schedule = [
    (9 * 60, 10 * 60),      # 9:00 to 10:00
    (11 * 60, 17 * 60)      # 11:00 to 5:00
]

# Create a Z3 solver instance
s = Solver()

# Define start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work starts
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work ends

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for Shirley's, Stephen's, and Paul's schedules
add_constraints(shirley_schedule, meeting_start)
add_constraints(stephen_schedule, meeting_start)
add_constraints(paul_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")