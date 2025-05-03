from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting interval [start, start+duration) must finish before the busy interval starts,
        # or it must start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Grace's busy intervals:
# 10:00 to 10:30 -> [600,630)
# 11:00 to 11:30 -> [660,690)
# 12:30 to 13:30 -> [750,810)
# 15:00 to 15:30 -> [900,930)
# 16:30 to 17:00 -> [990,1020)
grace_busy = [(600, 630), (660, 690), (750, 810), (900, 930), (990, 1020)]
add_busy_constraints(solver, grace_busy)

# Nicholas's busy intervals:
# 10:00 to 11:00 -> [600,660)
# 12:30 to 13:00 -> [750,780)
# 13:30 to 14:00 -> [810,840)
# 14:30 to 15:00 -> [870,900)
# 16:00 to 16:30 -> [960,990)
nicholas_busy = [(600, 660), (750, 780), (810, 840), (870, 900), (960, 990)]
add_busy_constraints(solver, nicholas_busy)

# Ann's busy intervals:
# 9:00 to 10:00   -> [540,600)
# 10:30 to 12:00  -> [630,720)
# 16:00 to 16:30  -> [960,990)
ann_busy = [(540, 600), (630, 720), (960, 990)]
add_busy_constraints(solver, ann_busy)

# Jacob is free the entire day so no busy intervals.

# Joe's busy intervals:
# 9:30 to 14:00   -> [570,840)
# 14:30 to 16:00  -> [870,960)
joe_busy = [(570, 840), (870, 960)]
add_busy_constraints(solver, joe_busy)

# Stephanie's busy intervals:
# 9:30 to 11:30   -> [570,690)
# 12:00 to 14:00  -> [720,840)
# 14:30 to 15:00  -> [870,900)
# 16:30 to 17:00  -> [990,1020)
stephanie_busy = [(570, 690), (720, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, stephanie_busy)

# Tyler's busy intervals:
# 9:00 to 14:00   -> [540,840)
# 14:30 to 16:30  -> [870,990)
tyler_busy = [(540, 840), (870, 990)]
add_busy_constraints(solver, tyler_busy)

# Iterate over possible start times within the allowed range to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):  # iterate over every minute from 9:00 until the latest possible start time.
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")