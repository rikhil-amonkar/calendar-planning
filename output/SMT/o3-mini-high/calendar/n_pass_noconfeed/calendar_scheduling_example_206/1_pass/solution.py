from z3 import *

# Convert minutes since midnight to HH:MM format string.
def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting duration in minutes.
meeting_duration = 30

# Define the meeting start time (in minutes from midnight).
# Monday working hours: 9:00 (540) to 17:00 (1020), but meeting must finish by 17:00.
# Margaret's preference: do not meet before 14:30 (870), so t >= 870.
t = Int('t')

solver = Solver()
solver.add(t >= 870, t + meeting_duration <= 1020)

# A helper function to enforce that meeting time [t, t+meeting_duration) does not overlap a busy interval [a, b).
def no_overlap(a, b):
    return Or(t + meeting_duration <= a, t >= b)

# Shirley's busy intervals on Monday (in minutes):
#   10:30 to 11:00  -> 630 to 660
#   12:00 to 12:30  -> 720 to 750
solver.add(no_overlap(630, 660))
solver.add(no_overlap(720, 750))

# Jacob's busy intervals:
#   9:00 to 9:30   -> 540 to 570
#   10:00 to 10:30 -> 600 to 630
#   11:00 to 11:30 -> 660 to 690
#   12:30 to 13:30 -> 750 to 810
#   14:30 to 15:00 -> 870 to 900
solver.add(no_overlap(540, 570))
solver.add(no_overlap(600, 630))
solver.add(no_overlap(660, 690))
solver.add(no_overlap(750, 810))
solver.add(no_overlap(870, 900))

# Stephen's busy intervals:
#   11:30 to 12:00 -> 690 to 720
#   12:30 to 13:00 -> 750 to 780
solver.add(no_overlap(690, 720))
solver.add(no_overlap(750, 780))

# Margaret's busy intervals:
#   9:00 to 9:30   -> 540 to 570
#   10:30 to 12:30 -> 630 to 750
#   13:00 to 13:30 -> 780 to 810
#   15:00 to 15:30 -> 900 to 930
#   16:30 to 17:00 -> 990 to 1020
solver.add(no_overlap(540, 570))
solver.add(no_overlap(630, 750))
solver.add(no_overlap(780, 810))
solver.add(no_overlap(900, 930))
solver.add(no_overlap(990, 1020))
# (Margaret's preference t >= 14:30 is already enforced by t >= 870.)

# Mason's busy intervals:
#   9:00 to 10:00  -> 540 to 600
#   10:30 to 11:00 -> 630 to 660
#   11:30 to 12:30 -> 690 to 750
#   13:00 to 13:30 -> 780 to 810
#   14:00 to 14:30 -> 840 to 870
#   16:30 to 17:00 -> 990 to 1020
solver.add(no_overlap(540, 600))
solver.add(no_overlap(630, 660))
solver.add(no_overlap(690, 750))
solver.add(no_overlap(780, 810))
solver.add(no_overlap(840, 870))
solver.add(no_overlap(990, 1020))

# Check for a solution.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[t].as_long()
    meeting_end = meeting_start + meeting_duration
    # Format output as HH:MM:HH:MM and include the day of the week.
    print("Monday " + minutes_to_str(meeting_start) + ":" + minutes_to_str(meeting_end))
else:
    print("No meeting time found.")