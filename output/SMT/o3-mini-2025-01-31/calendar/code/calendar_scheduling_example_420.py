from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time, in minutes since midnight

# The meeting must be within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so the meeting does not overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Enforce that the meeting either ends before a busy interval starts
        # or begins after the busy interval finishes.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Larry is busy from 16:00 to 17:00 (i.e., [960, 1020))
larry_busy = [(960, 1020)]
add_busy_constraints(solver, larry_busy)

# Elijah's busy intervals:
# 9:30 to 10:30 => [570, 630)
# 11:30 to 12:30 => [690, 750)
# 13:30 to 14:00 => [810, 840)
# 16:30 to 17:00 => [990, 1020)
elijah_busy = [(570, 630), (690, 750), (810, 840), (990, 1020)]
add_busy_constraints(solver, elijah_busy)

# Jean is free the entire day, so no constraints.

# Jesse is free the entire day, so no constraints.

# Walter's busy intervals:
# 9:30 to 10:30   => [570, 630)
# 11:30 to 12:00   => [690, 720)
# 13:00 to 14:00   => [780, 840)
# 15:00 to 16:30   => [900, 990)
walter_busy = [(570, 630), (690, 720), (780, 840), (900, 990)]
add_busy_constraints(solver, walter_busy)

# Keith's busy intervals:
# 9:00 to 9:30   => [540, 570)
# 10:30 to 11:00 => [630, 660)
# 11:30 to 12:30 => [690, 750)
# 14:00 to 15:00 => [840, 900)
# 15:30 to 16:00 => [930, 960)
# 16:30 to 17:00 => [990, 1020)
keith_busy = [(540, 570), (630, 660), (690, 750), (840, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, keith_busy)

# Ethan's busy intervals:
# 9:30 to 11:00 => [570, 660)
# 11:30 to 17:00 => [690, 1020)
ethan_busy = [(570, 660), (690, 1020)]
add_busy_constraints(solver, ethan_busy)

# Now, iterate over possible start times within the work window to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")