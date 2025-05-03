from z3 import Solver, Int, Or

# Create the Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting fits within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting must either finish by the busy interval's start or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Carl is free the entire day; no constraints added.

# Patrick's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
patrick_busy = [(540, 570), (690, 720)]
add_busy_constraints(solver, patrick_busy)

# Thomas is free the entire day; no constraints added.

# Bryan's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:30 to 13:00 -> [750, 780)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
bryan_busy = [(570, 600), (750, 780), (900, 930), (960, 990)]
add_busy_constraints(solver, bryan_busy)

# Matthew's busy intervals:
# 9:30 to 11:00  -> [570, 660)
# 11:30 to 13:30 -> [690, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:00 -> [900, 960)
matthew_busy = [(570, 660), (690, 810), (840, 870), (900, 960)]
add_busy_constraints(solver, matthew_busy)

# Bruce's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 12:30 to 16:30  -> [750, 990)
bruce_busy = [(540, 600), (630, 690), (750, 990)]
add_busy_constraints(solver, bruce_busy)

# William's busy intervals:
# 10:00 to 12:00 -> [600, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:30 -> [930, 990)
william_busy = [(600, 720), (750, 780), (840, 870), (930, 990)]
add_busy_constraints(solver, william_busy)

# Search for a valid meeting start time.
found = False
# Candidate start times from 540 minutes to 1020 - duration (inclusive).
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the solver state.
        break
    solver.pop()  # Restore the solver state if candidate fails.

if not found:
    print("No valid meeting time could be found.")