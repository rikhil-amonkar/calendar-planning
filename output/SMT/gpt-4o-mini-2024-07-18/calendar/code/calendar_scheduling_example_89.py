from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 60  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
michelle_schedule = [
    (11 * 60, 12 * 60),   # 11:00 to 12:00
    (14 * 60, 15 * 60)    # 14:00 to 15:00
]
andrea_schedule = [
    (9 * 60, 9.5 * 60),    # 9:00 to 9:30
    (11.5 * 60, 12.5 * 60), # 11:30 to 12:30
    (13 * 60, 14 * 60),     # 1:00 to 2:00
    (14.5 * 60, 15 * 60),   # 2:30 to 3:00
    (16 * 60, 16.5 * 60)    # 4:00 to 4:30
]
douglas_schedule = [
    (9 * 60, 9.5 * 60),     # 9:00 to 9:30
    (10 * 60, 10.5 * 60),   # 10:00 to 10:30
    (11 * 60, 15 * 60),     # 11:00 to 3:00
    (16 * 60, 17 * 60)      # 4:00 to 5:00
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

# Adding constraints for Michelle's, Andrea's, and Douglas's schedules
add_constraints(michelle_schedule, meeting_start)
add_constraints(andrea_schedule, meeting_start)
add_constraints(douglas_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")