from z3 import *

# Define meeting start time (in minutes from midnight)
s = Int('s')

solver = Solver()

# Working hours: meeting must be between 09:00 and 17:00.
# Helen also cannot meet after 15:00 and her busy block from 13:30 to 16:00 forces the meeting to finish by 13:30.
# Thus, we require the meeting (of 30 minutes) to start no earlier than 09:00 (540 minutes)
# and to end by 13:30 (810 minutes), i.e. s + 30 <= 810, so s <= 780.
solver.add(s >= 540)        # Meeting cannot start before 09:00.
solver.add(s + 30 <= 810)     # Meeting must end by 13:30 (which satisfies the after-15:00 constraint).

# Christine's busy intervals on Monday:
#   11:00 to 11:30 (minutes 660 to 690)
#   15:00 to 15:30 is irrelevant here because the meeting must end well before 15:00.
solver.add(Or(s + 30 <= 660, s >= 690))

# Helen's busy intervals on Monday:
#   9:30 to 10:30 -> [570, 630]
solver.add(Or(s + 30 <= 570, s >= 630))
#   11:00 to 11:30 -> [660, 690]
solver.add(Or(s + 30 <= 660, s >= 690))
#   12:00 to 12:30 -> [720, 750]
solver.add(Or(s + 30 <= 720, s >= 750))
#   13:30 to 16:00 -> [810, 960]
# For this interval the meeting must finish at or before 810.
solver.add(s + 30 <= 810)

# (The final busy interval [16:30,17:00] and work hours up to 17:00 are automatically respected.)

# Find a solution.
if solver.check() == sat:
    m = solver.model()
    start_time = m[s].as_long()
    end_time = start_time + 30

    # Convert minutes to HH:MM strings.
    start_hour = start_time // 60
    start_min = start_time % 60
    end_hour = end_time // 60
    end_min = end_time % 60

    time_range = f"{{{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}}}"
    day = "Monday"
    print(f"{day} {time_range}")
else:
    print("No valid meeting time found.")