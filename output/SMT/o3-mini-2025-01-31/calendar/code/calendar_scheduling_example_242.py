from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time, in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any busy interval provided.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either end before the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Anthony's busy intervals:
# 9:00 to 11:00  -> [540, 660)
# 15:00 to 16:00 -> [900, 960)
anthony_busy = [(540, 660), (900, 960)]
add_busy_constraints(solver, anthony_busy)

# Zachary's busy intervals:
# 12:30 to 14:00 -> [750, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:30 to 17:00 -> [990, 1020)
zachary_busy = [(750, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, zachary_busy)

# Russell's busy intervals:
# 9:00 to 10:00 -> [540, 600)
russell_busy = [(540, 600)]
add_busy_constraints(solver, russell_busy)

# Gary's busy intervals:
# 9:00 to 14:30 -> [540, 870)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
gary_busy = [(540, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, gary_busy)

# Helen's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 15:30  -> [780, 930)
# 16:30 to 17:00  -> [990, 1020)
helen_busy = [(540, 660), (690, 750), (780, 930), (990, 1020)]
add_busy_constraints(solver, helen_busy)

# Find the earliest meeting time that fits all constraints.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
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