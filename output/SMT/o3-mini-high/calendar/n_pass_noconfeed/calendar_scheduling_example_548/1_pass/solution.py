from z3 import *

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define meeting parameters
meeting_duration = 30  # in minutes
work_start = 9 * 60    # 9:00 in minutes
work_end = 17 * 60     # 17:00 in minutes

# Busy intervals for Nicole (in minutes):
# 9:00 to 10:00  ==> 540 to 600
# 10:30 to 16:30 ==> 630 to 990
busy1_start, busy1_end = 9 * 60, 10 * 60
busy2_start, busy2_end = 10 * 60 + 30, 16 * 60 + 30

# Preference: Nicole would rather not meet before 16:00 (960 minutes)
preferred_start = 16 * 60

# Create the Z3 solver and decision variable for the meeting start time (in minutes)
meeting_start = Int('meeting_start')
meeting_end = meeting_start + meeting_duration

s = Solver()

# Constraint: Meeting must be within work hours.
s.add(meeting_start >= work_start, meeting_end <= work_end)

# Constraint: Respect Nicole's existing meetings.
# The meeting must not overlap with the 9:00-10:00 busy slot.
s.add(Or(meeting_end <= busy1_start, meeting_start >= busy1_end))
# The meeting must not overlap with the 10:30-16:30 busy slot.
s.add(Or(meeting_end <= busy2_start, meeting_start >= busy2_end))

# Constraint: Meet Nicole's preference of not starting before 16:00.
s.add(meeting_start >= preferred_start)

# Solve the constraints.
if s.check() == sat:
    model = s.model()
    start = model[meeting_start].as_long()
    end = start + meeting_duration
    # Format and print the result.
    meeting_time_str = f"{minutes_to_time(start)}:{minutes_to_time(end)}"
    print("Monday")
    print(meeting_time_str)
else:
    print("No solution found.")