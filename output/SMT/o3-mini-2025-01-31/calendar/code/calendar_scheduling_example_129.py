from z3 import Optimize

# Create a Z3 optimizer instance.
opt = Optimize()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes. So, start should satisfy:
# start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
opt.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval (bs, be), the meeting [start, start+duration)
# must either finish by bs or start at/after be.
def add_busy_constraints(opt, busy_intervals):
    for bs, be in busy_intervals:
        opt.add((start + duration <= bs) | (start >= be))

# Jacqueline's busy intervals:
# 10:00 to 10:30 -> [600, 630]
# 11:00 to 11:30 -> [660, 690]
# 12:30 to 13:00 -> [750, 780]
# 14:00 to 15:00 -> [840, 900]
# 16:00 to 16:30 -> [960, 990]
jacqueline_busy = [
    (600, 630),
    (660, 690),
    (750, 780),
    (840, 900),
    (960, 990)
]
add_busy_constraints(opt, jacqueline_busy)

# Adam has no meetings, so no constraints are required for him.

# Gerald's busy intervals:
# 9:00 to 11:00   -> [540, 660]
# 11:30 to 12:00  -> [690, 720]
# 14:00 to 15:00  -> [840, 900]
# 15:30 to 17:00  -> [930, 1020]
gerald_busy = [
    (540, 660),
    (690, 720),
    (840, 900),
    (930, 1020)
]
add_busy_constraints(opt, gerald_busy)

# Wayne's busy intervals:
# 9:00 to 10:00   -> [540, 600]
# 10:30 to 11:30  -> [630, 690]
# 13:00 to 15:00  -> [780, 900]
# 15:30 to 16:00  -> [930, 960]
# 16:30 to 17:00  -> [990, 1020]
wayne_busy = [
    (540, 600),
    (630, 690),
    (780, 900),
    (930, 960),
    (990, 1020)
]
add_busy_constraints(opt, wayne_busy)

# We want the meeting at the earliest available time, so we minimize the start time.
opt.minimize(start)

# Check for a valid meeting time.
if opt.check() == sat:
    model = opt.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
        start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time could be found.")