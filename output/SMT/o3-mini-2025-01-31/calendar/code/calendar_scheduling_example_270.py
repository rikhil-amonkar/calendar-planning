from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Kimberly's preference: avoid meetings after 12:30.
# This implies that the meeting should finish by 12:30 (i.e., before 750 minutes).
solver.add(start + duration <= 750)

# Helper function to add constraints ensuring that the meeting [start, start+duration)
# does not overlap with any busy interval [busy_start, busy_end).
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish strictly before a busy interval starts or start after it finishes.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Frances's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 12:30 to 13:00 -> [750, 780)
frances_busy = [(540, 630), (750, 780)]
add_busy_constraints(solver, frances_busy)

# Aaron is free the entire day; no constraints needed.

# Rebecca is free the entire day; no constraints needed.

# Kimberly's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:00 to 13:30 -> [720, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
kimberly_busy = [(540, 570), (720, 810), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, kimberly_busy)

# Christopher's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 14:30 -> [660, 870)
# 15:30 to 17:00 -> [930, 1020)
christopher_busy = [(570, 630), (660, 870), (930, 1020)]
add_busy_constraints(solver, christopher_busy)

# Since Kimberly's preference forces the meeting to finish by 12:30,
# we only really need to consider start times that allow that.
solution_found = False
# Iterate over possible start times.
# Meeting must start no later than 750 - duration = 720 minutes.
for t in range(540, 720 + 1):  # from 540 to 720 inclusive.
    solver.push()  # Save current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")