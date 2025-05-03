from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
kelly_schedule = []          # Kelly is free all day
julia_schedule = [
    (9.5 * 60, 10 * 60),    # 9:30 to 10:00
    (14 * 60, 14.5 * 60),    # 14:00 to 14:30
    (15 * 60, 15.5 * 60),    # 15:00 to 15:30
    (16.5 * 60, 17 * 60)      # 16:30 to 17:00
]
martha_schedule = [
    (9 * 60, 11 * 60),      # 9:00 to 11:00
    (12 * 60, 15 * 60)      # 12:00 to 3:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Constraint for Julia's preference to avoid meetings after 13:30
s.add(meeting_start + meeting_duration <= 13.5 * 60)  # Meeting must end by 1:30 PM

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meetings start
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meetings end

# Adding constraints for Julia's and Martha's schedules
add_constraints(julia_schedule, meeting_start)
add_constraints(martha_schedule, meeting_start)
# No constraints for Kelly since she is available all day.

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")