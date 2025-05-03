from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting duration is 30 minutes, thus start must satisfy:
# start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Kathleen prefers not to meet before 13:30.
# 13:30 is 810 minutes from midnight.
solver.add(start >= 810)

# Helper function to ensure the meeting (start, start+duration) does not
# overlap with a given busy interval [bs, be).
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Kathleen's busy intervals:
# 13:00 to 14:00 -> [780, 840]
# 15:00 to 15:30 -> [900, 930]
# 16:00 to 16:30 -> [960, 990]
kathleen_busy = [(780, 840), (900, 930), (960, 990)]
add_busy_constraints(kathleen_busy)

# Frank has no meetings; thus no constraints are added for him.

# Christopher's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:00 to 11:30 -> [600, 690]
# 13:30 to 14:00 -> [810, 840]
# 15:30 to 17:00 -> [930, 1020]
christopher_busy = [(540, 570), (600, 690), (810, 840), (930, 1020)]
add_busy_constraints(christopher_busy)

# Kathryn's busy intervals:
# 9:00 to 10:00   -> [540, 600]
# 10:30 to 11:30  -> [630, 690]
# 12:30 to 13:00  -> [750, 780]
# 13:30 to 14:00  -> [810, 840]
# 14:30 to 15:00  -> [870, 900]
# 15:30 to 17:00  -> [930, 1020]
kathryn_busy = [(540, 600), (630, 690), (750, 780), (810, 840), (870, 900), (930, 1020)]
add_busy_constraints(kathryn_busy)

# Check for a valid meeting time that satisfies all constraints.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
          start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")