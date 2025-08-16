from z3 import *

# We represent time in minutes from midnight.
# Monday work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# The meeting lasts 30 minutes, so the start time T must be between 540 and 990 minutes (inclusive).

s = Solver()
T = Int('T')  # meeting start time in minutes

# Basic work hours constraint for the meeting start.
s.add(T >= 540, T <= 990)

# Anna's preference: she would rather not meet before 14:30 (14*60+30 = 870 minutes)
s.add(T >= 870)

# For each busy interval, we must ensure the meeting does not overlap.
# Two intervals [T, T+30] and [busy_start, busy_end] do not overlap if:
# Either the meeting ends on or before busy_start, or starts on or after busy_end.
# That is: Or(T + 30 <= busy_start, T >= busy_end)

# Adam's busy interval: 14:00 to 15:00 -> [840, 900]
s.add(Or(T + 30 <= 840, T >= 900))

# John's busy intervals:
# [13:00, 13:30] -> [780, 810]
s.add(Or(T + 30 <= 780, T >= 810))
# [14:00, 14:30] -> [840, 870]
s.add(Or(T + 30 <= 840, T >= 870))
# [15:30, 16:00] -> [930, 960]
s.add(Or(T + 30 <= 930, T >= 960))
# [16:30, 17:00] -> [990, 1020]
s.add(Or(T + 30 <= 990, T >= 1020))

# Stephanie's busy intervals:
# [9:30, 10:00] -> [570, 600]
s.add(Or(T + 30 <= 570, T >= 600))
# [10:30, 11:00] -> [630, 660]
s.add(Or(T + 30 <= 630, T >= 660))
# [11:30, 16:00] -> [690, 960]
s.add(Or(T + 30 <= 690, T >= 960))
# [16:30, 17:00] -> [990, 1020]
s.add(Or(T + 30 <= 990, T >= 1020))

# Anna's busy intervals:
# [9:30, 10:00] -> [570, 600]
s.add(Or(T + 30 <= 570, T >= 600))
# [12:00, 12:30] -> [720, 750]
s.add(Or(T + 30 <= 720, T >= 750))
# [13:00, 15:30] -> [780, 930]
s.add(Or(T + 30 <= 780, T >= 930))
# [16:30, 17:00] -> [990, 1020]
s.add(Or(T + 30 <= 990, T >= 1020))

if s.check() == sat:
    m = s.model()
    meeting_start = m[T].as_long()
    meeting_end = meeting_start + 30
    
    # Convert minutes to HH:MM format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60

    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
    print(f"End Time: {end_hour:02d}:{end_minute:02d}")
else:
    print("No solution found.")