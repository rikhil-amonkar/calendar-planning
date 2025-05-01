from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
denise_schedule = [
    (12 * 60, 12.5 * 60),  # 12:00 to 12:30
    (15.5 * 60, 16 * 60)    # 3:30 to 4:00
]
angela_schedule = []       # Angela is free all day
natalie_schedule = [
    (9 * 60, 11.5 * 60),    # 9:00 to 11:30
    (12 * 60, 13 * 60),     # 12:00 to 1:00
    (14 * 60, 14.5 * 60),   # 2:00 to 2:30
    (15 * 60, 17 * 60)      # 3:00 to 5:00
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
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meetings start
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meetings end

# Adding constraints for Denise's and Natalie's schedules
add_constraints(denise_schedule, meeting_start)
add_constraints(natalie_schedule, meeting_start)
# No constraints for Angela since she is available all day.

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")