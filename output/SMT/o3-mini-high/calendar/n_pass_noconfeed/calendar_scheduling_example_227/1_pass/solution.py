from z3 import *

# Meeting duration in minutes
duration = 30

# Define the meeting start time in minutes from midnight.
# The work day is from 9:00 (540) to 17:00 (1020) so that the meeting must satisfy:
# start >= 540 and start + duration <= 1020.
start = Int("start")

s = Solver()
s.add(start >= 540, start + duration <= 1020)

# David does not want to meet on Monday before 14:00 (14:00 = 840)
s.add(start >= 840)

# Helper function: For a busy interval [busy_start, busy_end], we must have either the meeting
# finish on or before busy_start or start on or after busy_end.
def no_overlap(busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Busy intervals are given in minutes (from midnight).

# Natalie is free all day, so no constraints for her.

# David's busy intervals:
#   11:30 - 12:00  -> 11*60+30 = 690, 12*60 = 720
#   14:30 - 15:00  -> 14*60+30 = 870, 15*60 = 900
s.add(no_overlap(690, 720))
s.add(no_overlap(870, 900))

# Douglas's busy intervals:
#   9:30 - 10:00   -> 9*60+30 = 570, 10*60 = 600
#   11:30 - 12:00  -> 690, 720
#   13:00 - 13:30  -> 13*60 = 780, 13*60+30 = 810
#   14:30 - 15:00  -> 870, 900
s.add(no_overlap(570, 600))
s.add(no_overlap(690, 720))
s.add(no_overlap(780, 810))
s.add(no_overlap(870, 900))

# Ralph's busy intervals:
#   9:00 - 9:30   -> 540, 570
#   10:00 - 11:00 -> 600, 660
#   11:30 - 12:30 -> 690, 750
#   13:30 - 15:00 -> 810, 900
#   15:30 - 16:00 -> 930, 960
#   16:30 - 17:00 -> 990, 1020
s.add(no_overlap(540, 570))
s.add(no_overlap(600, 660))
s.add(no_overlap(690, 750))
s.add(no_overlap(810, 900))
s.add(no_overlap(930, 960))
s.add(no_overlap(990, 1020))

# Jordan's busy intervals:
#   9:00 - 10:00   -> 540, 600
#   12:00 - 12:30  -> 720, 750
#   13:00 - 13:30  -> 780, 810
#   14:30 - 15:00  -> 870, 900
#   15:30 - 17:00  -> 930, 1020
s.add(no_overlap(540, 600))
s.add(no_overlap(720, 750))
s.add(no_overlap(780, 810))
s.add(no_overlap(870, 900))
s.add(no_overlap(930, 1020))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    meeting_start = m[start].as_long()
    meeting_end = meeting_start + duration

    # Function to convert minutes since midnight to "HH:MM" format.
    def minutes_to_time(m):
        hours = m // 60
        minutes = m % 60
        return f"{hours:02d}:{minutes:02d}"

    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    # The meeting is on Monday.
    print(f"Monday {start_str}:{end_str}")
else:
    print("No solution found")