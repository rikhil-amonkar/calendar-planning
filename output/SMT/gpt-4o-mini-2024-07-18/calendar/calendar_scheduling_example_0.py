from z3 import *

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 60  # 1 hour in minutes

# Define existing schedules in minutes
michelle_schedule = [(11 * 60, 12 * 60)]
steven_schedule = [(9 * 60, 9.5 * 60), (11.5 * 60, 12 * 60), (13.5 * 60, 14 * 60), (15.5 * 60, 16 * 60)]
jerry_schedule = [(9 * 60, 9.5 * 60), (10 * 60, 11 * 60), (11.5 * 60, 12.5 * 60), (13 * 60, 14.5 * 60), (15.5 * 60, 16 * 60), (16.5 * 60, 17 * 60)]

# Create a Z3 solver instance
s = Solver()

# Define the variable for the start time of the meeting
meeting_start = Int('meeting_start')
s.add(meeting_start >= work_start)
s.add(meeting_start + meeting_duration <= work_end)

# Create constraints based on participant schedules
def add_constraints(schedule, meeting_start):
    for start, end in schedule:
        s.add(meeting_start + meeting_duration <= start)  # Meeting ends before the participant's meeting starts
        s.add(meeting_start >= end)  # Meeting starts after the participant's meeting ends

# Adding constraints for each participant
add_constraints(michelle_schedule, meeting_start)
add_constraints(steven_schedule, meeting_start)
add_constraints(jerry_schedule, meeting_start)

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    print(f"Meeting can be scheduled starting at {start_time // 60}:{start_time % 60:02d}.")
else:
    print("No possible time found for the meeting.")