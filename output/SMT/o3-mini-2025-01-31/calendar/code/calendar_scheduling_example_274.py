from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.

duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: Adds constraints to ensure the meeting does not overlap with a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting is valid if it ends before a busy interval starts or begins after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Kevin's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 17:00 -> [960, 1020)
kevin_busy = [(690, 720), (840, 870), (960, 1020)]
add_busy_constraints(solver, kevin_busy)

# Joyce is free the entire day (no busy intervals).

# Kathryn's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
kathryn_busy = [(540, 570), (690, 720)]
add_busy_constraints(solver, kathryn_busy)

# Bruce's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 13:30  -> [660, 810)
# 14:00 to 17:00  -> [840, 1020)
bruce_busy = [(540, 630), (660, 810), (840, 1020)]
add_busy_constraints(solver, bruce_busy)

# Ronald's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 13:30  -> [690, 810)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
ronald_busy = [(570, 660), (690, 810), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, ronald_busy)

# Try to find a valid meeting start time from 9:00 to the last possible start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore the state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")