from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
bradley_schedule = [
    (9.5 * 60, 10 * 60),   # 9:30 to 10:00
    (13 * 60, 13.5 * 60),  # 1:00 to 1:30
    (14.5 * 60, 15 * 60),  # 2:30 to 3:00
    (16.5 * 60, 17 * 60)   # 4:30 to 5:00
]
andrew_schedule = [
    (9 * 60, 9.5 * 60),    # 9:00 to 9:30
    (12.5 * 60, 13.5 * 60), # 12:30 to 1:30
    (14 * 60, 14.5 * 60),  # 2:00 to 2:30
    (15 * 60, 16 * 60)     # 3:00 to 4:00
]
melissa_schedule = [
    (9 * 60, 9.5 * 60),    # 9:00 to 9:30
    (10 * 60, 10.5 * 60),  # 10:00 to 10:30
    (11 * 60, 14 * 60),    # 11:00 to 2:00
    (15 * 60, 15.5 * 60),  # 3:00 to 3:30
    (16 * 60, 16.5 * 60)   # 4:00 to 4:30
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

# Adding constraints for Bradley's, Andrew's, and Melissa's schedules
add_constraints(bradley_schedule, meeting_start)
add_constraints(andrew_schedule, meeting_start)
add_constraints(melissa_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")