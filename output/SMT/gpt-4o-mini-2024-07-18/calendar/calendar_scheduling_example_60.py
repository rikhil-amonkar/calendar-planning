from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
lisa_schedule = [
    (10.5 * 60, 11 * 60),  # 10:30 to 11:00
    (11.5 * 60, 12 * 60),  # 11:30 to 12:00
    (14 * 60, 15 * 60)     # 2:00 to 3:00
]
dorothy_schedule = []     # Dorothy is free all day
raymond_schedule = [
    (9 * 60, 10 * 60),      # 9:00 to 10:00
    (10.5 * 60, 11 * 60),   # 10:30 to 11:00
    (11.5 * 60, 15 * 60),   # 11:30 to 3:00
    (16 * 60, 17 * 60)      # 4:00 to 5:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Constraint for Dorothy's preference to avoid meetings after 10:30
s.add(meeting_start + meeting_duration <= 10.5 * 60)  # Meeting must end by 10:30

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meeting starts
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Add constraints for Lisa's and Raymond's schedules
add_constraints(lisa_schedule, meeting_start)
add_constraints(raymond_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")