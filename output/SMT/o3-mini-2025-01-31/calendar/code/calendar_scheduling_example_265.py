from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before a busy interval begins or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Cheryl is free the entire day so no constraints.

# Juan's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 12:00 to 13:00  -> [720, 780)
# 14:00 to 14:30  -> [840, 870)
# 16:00 to 17:00  -> [960, 1020)
juan_busy = [(570, 600), (720, 780), (840, 870), (960, 1020)]
add_busy_constraints(solver, juan_busy)

# Alan has no meetings the whole day, so no constraints.

# Christina's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 12:00 to 14:30  -> [720, 870)
# 15:00 to 16:00  -> [900, 960)
christina_busy = [(540, 630), (720, 870), (900, 960)]
add_busy_constraints(solver, christina_busy)

# Grace's busy intervals:
# 9:00 to 14:00   -> [540, 840)
# 15:00 to 17:00  -> [900, 1020)
grace_busy = [(540, 840), (900, 1020)]
add_busy_constraints(solver, grace_busy)

# Now, search for a valid meeting start time.
solution_found = False
# Iterate over all possible start times (in minutes) within [540, 1020-duration]
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current solver state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore solver state
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")