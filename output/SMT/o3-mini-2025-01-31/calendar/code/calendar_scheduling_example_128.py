from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes, so we require start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Harold cannot meet on Monday before 14:00,
# 14:00 is 840 minutes from midnight.
solver.add(start >= 840)

# Helper function to add constraints ensuring that
# the meeting (start, start+duration) does not overlap with a busy interval.
def add_busy_constraints(busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Catherine's busy intervals:
# 9:00 to 10:00   -> [540, 600]
# 13:00 to 13:30  -> [780, 810]
# 14:00 to 15:00  -> [840, 900]
# 16:00 to 16:30  -> [960, 990]
catherine_busy = [
    (540, 600),
    (780, 810),
    (840, 900),
    (960, 990)
]
add_busy_constraints(catherine_busy)

# Harold's busy intervals:
# 12:30 to 13:00  -> [750, 780]
# 15:00 to 15:30  -> [900, 930]
harold_busy = [
    (750, 780),
    (900, 930)
]
add_busy_constraints(harold_busy)

# Ann's busy intervals:
# 9:30 to 10:30   -> [570, 630]
# 11:00 to 11:30  -> [660, 690]
# 12:30 to 13:00  -> [750, 780]
# 14:00 to 15:30  -> [840, 930]
# 16:00 to 16:30  -> [960, 990]
ann_busy = [
    (570, 630),
    (660, 690),
    (750, 780),
    (840, 930),
    (960, 990)
]
add_busy_constraints(ann_busy)

# Randy's busy intervals:
# 9:00 to 12:00   -> [540, 720]
# 13:00 to 14:00  -> [780, 840]
# 14:30 to 15:30  -> [870, 930]
# 16:00 to 17:00  -> [960, 1020]
randy_busy = [
    (540, 720),
    (780, 840),
    (870, 930),
    (960, 1020)
]
add_busy_constraints(randy_busy)

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