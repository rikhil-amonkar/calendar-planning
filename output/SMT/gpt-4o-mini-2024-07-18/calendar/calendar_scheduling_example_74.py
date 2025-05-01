from z3 import *

# Define working hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
eric_schedule = [
    (10 * 60, 12 * 60)     # 10:00 to 12:00
]
albert_schedule = [
    (12 * 60, 12.5 * 60),  # 12:00 to 12:30
    (15.5 * 60, 16 * 60)    # 3:30 to 4:00
]
katherine_schedule = [
    (10 * 60, 11 * 60),     # 10:00 to 11:00
    (11.5 * 60, 14 * 60),   # 11:30 to 2:00
    (15 * 60, 15.5 * 60)    # 3:00 to 3:30
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Constraint for Eric's preference to avoid meetings after 15:30
s.add(meeting_start + meeting_duration <= 15.5 * 60)  # Meeting must end by 3:30 PM

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meetings start
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meetings end

# Adding constraints for Eric's, Albert's, and Katherine's schedules
add_constraints(eric_schedule, meeting_start)
add_constraints(albert_schedule, meeting_start)
add_constraints(katherine_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")