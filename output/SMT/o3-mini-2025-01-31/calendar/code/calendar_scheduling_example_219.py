from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a participant's busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must end before a busy interval starts
        # OR start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Thomas's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:30 -> [870, 930)
thomas_busy = [(540, 570), (600, 660), (690, 720), (870, 930)]
add_busy_constraints(solver, thomas_busy)

# Terry's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 14:00 -> [780, 840)
# 15:00 to 15:30 -> [900, 930)
terry_busy = [(720, 750), (780, 840), (900, 930)]
add_busy_constraints(solver, terry_busy)

# Kenneth's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:30 -> [750, 810)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 17:00 -> [960, 1020)
kenneth_busy = [(690, 720), (750, 810), (840, 870), (960, 1020)]
add_busy_constraints(solver, kenneth_busy)

# Andrew's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:00 to 14:00  -> [720, 840)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 17:00  -> [960, 1020)
andrew_busy = [(570, 600), (630, 690), (720, 840), (900, 930), (960, 1020)]
add_busy_constraints(solver, andrew_busy)

# Sharon's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:30 to 13:00  -> [690, 780)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 16:30  -> [960, 990)
sharon_busy = [(540, 630), (690, 780), (810, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, sharon_busy)

# Search for the earliest valid meeting time.
solution_found = False
# Latest valid start is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # save current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")