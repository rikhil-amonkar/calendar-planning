from z3 import *

# We will represent meeting start time in minutes after midnight.
# For Monday, the working hours are 09:00 (540 minutes) to 17:00 (1020 minutes).
# The meeting lasts 30 minutes.
# In addition, Helen cannot meet after 15:00 (900 minutes) and her calendar blocks
# 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:30-16:00, 16:30-17:00.
# Christine’s calendar blocks 11:00-11:30 and 15:00-15:30.
# (Note: Since the meeting must finish before Helen’s busy block at 13:30,
#   any meeting scheduled later than 13:30 would conflict with her block 13:30-16:00.
#   Also, the extra “cannot meet after 15:00” is automatically enforced by her blocked times.)

# Define the meeting start variable.
meeting_start = Int('meeting_start')
meeting_duration = 30
meeting_end = meeting_start + meeting_duration

# Create the solver.
s = Solver()

# Global working hours for the meeting (we also add Helen's extra constraint)
s.add(meeting_start >= 9 * 60)         # >= 09:00 (540)
s.add(meeting_end <= 17 * 60)          # <= 17:00 (1020)
s.add(meeting_end <= 15 * 60)          # Helen cannot meet after 15:00 (i.e. meeting must finish by 15:00)

# Now add the non-overlap (availability) constraints for each participant.
# Two intervals [a,b) and [c,d) do not overlap if: b <= c or a >= d.
#
# For Christine, the only relevant busy block in our time-window is 11:00-11:30:
#   11:00 is 660 minutes; 11:30 is 690 minutes.
s.add(Or(meeting_end <= 660, meeting_start >= 690))
# (Christine’s meeting at 15:00-15:30 is automatically avoided since meeting_end <= 900)

# For Helen, her busy intervals (in minutes) are:
#   9:30 - 10:30  : 570 to 630
#   11:00 - 11:30 : 660 to 690
#   12:00 - 12:30 : 720 to 750
#   13:30 - 16:00 : 810 to 960
#   16:30 - 17:00 : 990 to 1020 (won't affect us because meeting_end <= 15:00)
#
# For each busy interval, the meeting must lie entirely before the block or entirely after it.
s.add(Or(meeting_end <= 570, meeting_start >= 630))  # Avoid 9:30-10:30
s.add(Or(meeting_end <= 660, meeting_start >= 690))  # Avoid 11:00-11:30
s.add(Or(meeting_end <= 720, meeting_start >= 750))  # Avoid 12:00-12:30
s.add(Or(meeting_end <= 810, meeting_start >= 960))  # Avoid 13:30-16:00

# Since meeting_end must be <= 15:00 (900 minutes) and meeting is 30 minutes long,
# the latest meeting_start would be 870. However, the last busy block forces meeting_end <= 810,
# so in effect meeting_start can be at most 780.
# (This also ensures meeting fits completely into one of Helen's available free slots:
#   9:00-9:30, 10:30-11:00, 11:30-12:00, or 12:30-13:30.)

# Check for a solution.
if s.check() == sat:
    m = s.model()
    start_val = m[meeting_start].as_long()
    end_val = start_val + meeting_duration

    # Helper function to convert minutes to HH:MM (24-hour format)
    def format_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", format_time(start_val))
    print("End Time:", format_time(end_val))
else:
    print("No valid meeting time found.")