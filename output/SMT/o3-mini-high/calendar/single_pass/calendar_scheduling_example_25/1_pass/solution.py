from z3 import *

# Convert times to minutes since midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
work_start = 9 * 60      # 540
work_end   = 17 * 60     # 1020
# Pamela's preference: do not meet after 14:30 (870 minutes)
pamela_deadline = 14 * 60 + 30  # 870

# Meeting duration is 60 minutes.
duration = 60

# Define an integer variable for the meeting start time (in minutes).
meeting_start = Int('meeting_start')
meeting_end = meeting_start + duration

# Constraints: meeting must be within work hours and satisfy Pamela's no-after-14:30.
constraints = [
    meeting_start >= work_start,
    meeting_end <= work_end,
    meeting_end <= pamela_deadline  # ensures meeting ends by 14:30
]

# Define the busy intervals for each participant (in minutes).
# Each busy interval is a tuple (start_time, end_time). We assume that if a meeting ends exactly when
# another starts, that is acceptable (non-overlapping).

# Anthony's busy intervals on Monday:
# 9:30 - 10:00, 12:00 - 13:00, 16:00 - 16:30
anthony_busy = [
    (9 * 60 + 30, 10 * 60),     # 570 to 600
    (12 * 60, 13 * 60),         # 720 to 780
    (16 * 60, 16 * 60 + 30)     # 960 to 990
]

# Pamela's busy intervals on Monday:
# 9:30 - 10:00, 16:30 - 17:00
pamela_busy = [
    (9 * 60 + 30, 10 * 60),     # 570 to 600
    (16 * 60 + 30, 17 * 60)     # 990 to 1020
]

# Zachary's busy intervals on Monday:
# 9:00 - 11:30, 12:00 - 12:30, 13:00 - 13:30, 14:30 - 15:00, 16:00 - 17:00
zachary_busy = [
    (9 * 60, 11 * 60 + 30),     # 540 to 690
    (12 * 60, 12 * 60 + 30),    # 720 to 750
    (13 * 60, 13 * 60 + 30),    # 780 to 810
    (14 * 60 + 30, 15 * 60),    # 870 to 900
    (16 * 60, 17 * 60)          # 960 to 1020
]

# A helper function: For a meeting not to conflict with an existing busy interval,
# the meeting must finish before the busy interval starts or start after the busy interval ends.
def no_overlap(meeting_start, meeting_end, busy_start, busy_end):
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

# Add non-overlap constraints for each busy interval of each participant.
for (bs, be) in anthony_busy:
    constraints.append(no_overlap(meeting_start, meeting_end, bs, be))

for (bs, be) in pamela_busy:
    constraints.append(no_overlap(meeting_start, meeting_end, bs, be))

for (bs, be) in zachary_busy:
    constraints.append(no_overlap(meeting_start, meeting_end, bs, be))

# Create the Z3 solver and add all constraints.
solver = Solver()
solver.add(constraints)

# Try to find a solution.
if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + duration
    start_hour, start_minute = divmod(start_val, 60)
    end_hour, end_minute = divmod(end_val, 60)
    
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: {:02d}:{:02d}".format(start_hour, start_minute))
    print("End Time: {:02d}:{:02d}".format(end_hour, end_minute))
else:
    print("No solution found.")