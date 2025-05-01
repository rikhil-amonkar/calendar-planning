from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
ryan_schedule = [
    (9 * 60, 9.5 * 60),  # 9:00 to 9:30
    (12.5 * 60, 13 * 60) # 12:30 to 1:00
]
ruth_schedule = []      # Ruth is free all day
denise_schedule = [
    (9.5 * 60, 10.5 * 60), # 9:30 to 10:30
    (12 * 60, 13 * 60),     # 12:00 to 1:00
    (14.5 * 60, 16.5 * 60)  # 2:30 to 4:30
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Start time cannot be before working hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Constraint for Denise's preference to avoid meetings after 12:30
s.add(meeting_start + meeting_duration <= 12.5 * 60)  # Meeting must end by 12:30

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for Ryan's and Denise's schedules
add_constraints(ryan_schedule, meeting_start)
add_constraints(denise_schedule, meeting_start)
# No constraints added for Ruth since she is free all day.

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")