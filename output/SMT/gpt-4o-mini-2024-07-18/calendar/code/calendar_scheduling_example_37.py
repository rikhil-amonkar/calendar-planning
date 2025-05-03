from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
gregory_schedule = [
    (11 * 60, 11.5 * 60),  # 11:00 to 11:30
    (12 * 60, 12.5 * 60),  # 12:00 to 12:30
    (15.5 * 60, 16.5 * 60)  # 15:30 to 16:30
]
teresa_schedule = []      # Teresa is free all day
carol_schedule = [
    (9 * 60, 10.5 * 60),   # 9:00 to 10:30
    (11 * 60, 16 * 60),    # 11:00 to 4:00
    (16.5 * 60, 17 * 60)   # 16:30 to 17:00
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
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meeting ends

# Adding constraints for Gregory's and Carol's schedules
add_constraints(gregory_schedule, meeting_start)
add_constraints(carol_schedule, meeting_start)
# No constraints added for Teresa since she is free all day.

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")