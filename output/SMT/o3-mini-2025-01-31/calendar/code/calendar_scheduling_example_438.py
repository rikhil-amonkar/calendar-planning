from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either finish before the busy period starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# George's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
george_busy = [(690, 720), (900, 930), (960, 1020)]
add_busy_constraints(solver, george_busy)

# Jesse's calendar is wide open (no constraints).

# Emma's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
emma_busy = [(570, 600), (660, 690), (720, 750), (900, 930), (960, 1020)]
add_busy_constraints(solver, emma_busy)

# Christian's calendar is wide open (no constraints).

# Ashley's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:30 -> [600, 750)
# 14:30 to 15:30 -> [870, 930)
ashley_busy = [(540, 570), (600, 750), (870, 930)]
add_busy_constraints(solver, ashley_busy)

# Jose's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 13:30  -> [690, 810)
# 14:30 to 16:30  -> [870, 990)
jose_busy = [(540, 660), (690, 810), (870, 990)]
add_busy_constraints(solver, jose_busy)

# Charles's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 12:00 to 14:00  -> [720, 840)
# 14:30 to 15:30  -> [870, 930)
# 16:30 to 17:00  -> [990, 1020)
charles_busy = [(540, 600), (630, 660), (720, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, charles_busy)

# Search for a valid meeting start time by checking each possible minute.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}.".format(
            start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")