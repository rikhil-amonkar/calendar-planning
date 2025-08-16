from z3 import *

# We represent time in minutes from midnight.
# Work hours: 9:00 = 540, 17:00 = 1020.
# Evelyn does not want meetings after 13:00, so the meeting must finish by 13:00 (780).
# Meeting duration is 30 minutes.

meeting_duration = 30

# Create an integer variable for the meeting start time (in minutes from midnight)
s = Int('s')

# Establish the overall constraints:
# 1. The meeting must be within work hours and finish by 13:00.
work_hours = And(s >= 540, s + meeting_duration <= 1020, s + meeting_duration <= 780)

# 2. Randy's busy intervals (in minutes):
#    - Busy from 9:00 to 10:30    --> [540, 630]
#    - Busy from 11:00 to 15:30   --> [660, 930]
#    - Busy from 16:00 to 17:00   --> [960, 1020]
#
# The meeting (interval [s, s+30]) must not overlap any busy interval.
def no_overlap(s, busy_start, busy_end):
    # Meeting [s, s+meeting_duration] does not overlap [busy_start, busy_end]
    return Or(s + meeting_duration <= busy_start, s >= busy_end)

busy1 = no_overlap(s, 540, 630)
busy2 = no_overlap(s, 660, 930)
busy3 = no_overlap(s, 960, 1020)

# Set up the solver
solver = Solver()
solver.add(work_hours, busy1, busy2, busy3)

if solver.check() == sat:
    m = solver.model()
    meeting_start = m[s].as_long()
    meeting_end = meeting_start + meeting_duration

    # A helper function to convert minutes to HH:MM in 24-hour format.
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # According to the constraints, the only valid solution is in Randy's free slot
    # between 10:30 and 11:00.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", format_time(meeting_start))
    print("End Time:", format_time(meeting_end))
else:
    print("No solution found")