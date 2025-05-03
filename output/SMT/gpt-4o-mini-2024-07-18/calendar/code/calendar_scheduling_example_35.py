from z3 import *

# Define work hours in minutes
work_start = 9 * 60  # 9:00 AM in minutes
work_end = 17 * 60   # 5:00 PM in minutes
meeting_duration = 30  # Meeting duration in minutes

# Define existing schedules for each participant in minutes
bradley_schedule = []  # Bradley is free all day
zachary_schedule = [
    (10 * 60, 10.5 * 60),  # 10:00 to 10:30
    (15 * 60, 15.5 * 60)    # 15:00 to 15:30
]
teresa_schedule = [
    (9 * 60, 10.5 * 60),    # 9:00 to 10:30
    (11 * 60, 12.5 * 60),   # 11:00 to 12:30
    (13 * 60, 14 * 60),     # 13:00 to 14:00
    (14.5 * 60, 16.5 * 60)  # 14:30 to 16:30
]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)  # Meeting cannot start before work hours
s.add(meeting_start + meeting_duration <= work_end)  # Meeting must finish before work hours end

# Constraint for Bradley's preference to avoid meetings before 14:30
s.add(meeting_start + meeting_duration <= 14.5 * 60)  # Meeting must end by 14:30

# Function to add participant constraints
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting must end before this participant's meetings start
        s.add(meeting_start >= end)                        # Meeting must start after this participant's meetings end

# Adding constraints for Zachary's and Teresa's schedules
add_constraints(zachary_schedule, meeting_start)
add_constraints(teresa_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")