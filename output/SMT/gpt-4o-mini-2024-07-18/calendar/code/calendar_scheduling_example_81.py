from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
jeremy_schedule = [
    (14.5 * 60, 15.5 * 60)  # 14:30 to 15:30
]
lawrence_schedule = [
    (15.5 * 60, 16 * 60),    # 15:30 to 16:00
    (16.5 * 60, 17 * 60)     # 16:30 to 17:00
]
helen_schedule = [
    (9.5 * 60, 10 * 60),      # 9:30 to 10:00
    (10.5 * 60, 11 * 60),     # 10:30 to 11:00
    (11.5 * 60, 12 * 60),     # 11:30 to 12:00
    (13 * 60, 14 * 60),       # 1:00 to 2:00
    (15 * 60, 15.5 * 60),     # 3:00 to 3:30
    (16 * 60, 17 * 60)        # 4:00 to 5:00
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Function to add constraints for participant schedules
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meetings start
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meetings end

# Adding constraints for Jeremy's, Lawrence's, and Helen's schedules
add_constraints(jeremy_schedule, meeting_start)
add_constraints(lawrence_schedule, meeting_start)
add_constraints(helen_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")