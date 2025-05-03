from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Meeting parameters:
# Working hours: 09:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes
# Grace's preference: avoid meetings after 15:00, so the meeting must finish by 15:00 (i.e., start + 30 <= 15:00 -> 900 minutes).
start = Int('start')
solver.add(start >= 540, start + 30 <= 900)

# Helper function to add constraints ensuring the meeting does not overlap a busy interval.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        # The meeting (from start to start+30) should either end at or before bs,
        # or start at or after be.
        solver.add(Or(start + 30 <= bs, start >= be))

# Grace's calendar is free, but her meeting preference is already captured above.

# Alexis has no meetings.

# Helen's busy intervals:
# 9:00 to 12:00    -> [540, 720]
# 12:30 to 14:00   -> [750, 840]
# 14:30 to 15:00   -> [870, 900]
# 15:30 to 16:00   -> [930, 960]  (beyond 15:00, but added for completeness)
# 16:30 to 17:00   -> [990, 1020] (beyond 15:00, but added for completeness)
helen_busy = [(540, 720), (750, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(helen_busy)

# Ashley's busy intervals:
# 9:00 to 9:30    -> [540, 570]
# 10:00 to 10:30  -> [600, 630]
# 11:00 to 14:00  -> [660, 840]
# 14:30 to 15:00  -> [870, 900]
# 15:30 to 17:00  -> [930, 1020] (beyond our applicable range)
ashley_busy = [(540, 570), (600, 630), (660, 840), (870, 900), (930, 1020)]
add_busy_constraints(ashley_busy)

# Find a meeting time that satisfies all the constraints
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + 30
    start_hour = meeting_start // 60
    start_min = meeting_start % 60
    end_hour = meeting_end // 60
    end_min = meeting_end % 60
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")