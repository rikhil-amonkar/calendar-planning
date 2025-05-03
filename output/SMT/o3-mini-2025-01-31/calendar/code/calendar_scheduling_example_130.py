from z3 import Optimize

# Create a Z3 optimizer instance.
opt = Optimize()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes).
# Meeting duration: 30 minutes, so start must satisfy:
# start >= 540 and start + 30 <= 1020.
duration = 30
start = Int('start')
opt.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting
# [start, start+duration) does not overlap with a given busy interval [bs, be).
def add_busy_constraints(optimizer, busy_intervals):
    for bs, be in busy_intervals:
        optimizer.add(Or(start + duration <= bs, start >= be))

# John's busy intervals:
# 9:00 to 9:30 -> [540, 570]
# 10:00 to 10:30 -> [600, 630]
# 11:00 to 11:30 -> [660, 690]
# 13:00 to 14:30 -> [780, 870]
john_busy = [
    (540, 570),
    (600, 630),
    (660, 690),
    (780, 870)
]
add_busy_constraints(opt, john_busy)

# Ralph's busy intervals:
# 13:30 to 14:00 -> [810, 840]
# 14:30 to 15:00 -> [870, 900]
# 15:30 to 16:30 -> [930, 990]
ralph_busy = [
    (810, 840),
    (870, 900),
    (930, 990)
]
add_busy_constraints(opt, ralph_busy)

# Daniel's busy intervals:
# 9:00 to 9:30   -> [540, 570]
# 10:30 to 11:00 -> [630, 660]
# 12:00 to 13:00 -> [720, 780]
# 13:30 to 16:30 -> [810, 990]
daniel_busy = [
    (540, 570),
    (630, 660),
    (720, 780),
    (810, 990)
]
add_busy_constraints(opt, daniel_busy)

# Keith's busy intervals:
# 10:30 to 14:30 -> [630, 870]
# 15:00 to 17:00 -> [900, 1020]
keith_busy = [
    (630, 870),
    (900, 1020)
]
add_busy_constraints(opt, keith_busy)

# We want the meeting at the earliest available time,
# so we minimize the start time.
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