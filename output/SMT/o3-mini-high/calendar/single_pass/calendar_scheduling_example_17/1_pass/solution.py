from z3 import *

# We'll represent time in minutes from midnight.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting duration is 30 minutes.
# Helen doesn’t want meetings after 13:30 (810 minutes).
# Thus meeting_end (start + 30) must be <= 810, i.e. meeting_start <= 780.

s = Solver()
meeting_start = Int('meeting_start')
duration = 30
meeting_end = meeting_start + duration

# Global working hours constraints
s.add(meeting_start >= 540)         # not before 9:00
s.add(meeting_end <= 1020)          # not after 17:00

# Helen's preference constraint: meeting must finish by 13:30 (810 minutes)
s.add(meeting_end <= 810)

# Blocked intervals are modeled as tuples (start, end) in minutes.
# For two intervals [a, b) and [c, d) to not overlap,
# either meeting_end <= block_start or meeting_start >= block_end must hold.

# Margaret's blocked times on Monday:
# 9:00-10:00, 10:30-11:00, 11:30-12:00, 13:00-13:30, 15:00-15:30
margaret_blocks = [
    (540, 600),   # 9:00 to 10:00
    (630, 660),   # 10:30 to 11:00
    (690, 720),   # 11:30 to 12:00
    (780, 810),   # 13:00 to 13:30
    (900, 930)    # 15:00 to 15:30
]

# Donna's blocked times on Monday:
# 14:30-15:00, 16:00-16:30
donna_blocks = [
    (870, 900),   # 14:30 to 15:00
    (960, 990)    # 16:00 to 16:30
]

# Helen's blocked times on Monday:
# 9:00-9:30, 10:00-11:30, 13:00-14:00, 14:30-15:00, 15:30-17:00
helen_blocks = [
    (540, 570),   # 9:00 to 9:30
    (600, 690),   # 10:00 to 11:30
    (780, 840),   # 13:00 to 14:00
    (870, 900),   # 14:30 to 15:00
    (930, 1020)   # 15:30 to 17:00
]

# Function to add a no-overlap constraint for each blocked interval.
def add_no_overlap(blocks):
    for (block_start, block_end) in blocks:
        s.add(Or(meeting_end <= block_start, meeting_start >= block_end))

# Add constraints for each participant.
add_no_overlap(margaret_blocks)
add_no_overlap(donna_blocks)
add_no_overlap(helen_blocks)

# Check if the problem is satisfiable and print the solution.
if s.check() == sat:
    m = s.model()
    start_val = m[meeting_start].as_long()
    end_val = start_val + duration

    # Convert minutes to HH:MM (24-hour format)
    start_hour = start_val // 60
    start_min = start_val % 60
    end_hour = end_val // 60
    end_min = end_val % 60

    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: {:02d}:{:02d}".format(start_hour, start_min))
    print("End Time: {:02d}:{:02d}".format(end_hour, end_min))
else:
    print("No solution found.")