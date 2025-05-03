from z3 import Solver, Int, Or

# Create a solver instance
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time (in minutes since midnight)

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that prevent overlapping a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting [start, start+duration) must be scheduled completely before
        # a busy interval starts or completely after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Edward's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 16:00 to 16:30 -> [960, 990)
edward_busy = [(690, 720), (960, 990)]
add_busy_constraints(solver, edward_busy)

# Samantha's busy intervals:
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
samantha_busy = [(840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, samantha_busy)

# Jacob's busy intervals:
# 11:30 to 13:30 -> [690, 810)
# 16:00 to 17:00 -> [960, 1020)
jacob_busy = [(690, 810), (960, 1020)]
add_busy_constraints(solver, jacob_busy)

# Vincent's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
vincent_busy = [(570, 600), (660, 690), (720, 750), (780, 810), (900, 930), (990, 1020)]
add_busy_constraints(solver, vincent_busy)

# William's busy intervals:
# 9:00 to 14:00  -> [540, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
william_busy = [(540, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, william_busy)

# Alexander's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 13:30 -> [660, 810)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
alexander_busy = [(540, 630), (660, 810), (870, 930), (960, 1020)]
add_busy_constraints(solver, alexander_busy)

# Dylan's busy intervals:
# 9:30 to 12:00  -> [570, 720)
# 12:30 to 14:30 -> [750, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
dylan_busy = [(570, 720), (750, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, dylan_busy)

# Iterate through potential starting times.
found = False
for t in range(540, 1020 - duration + 1):  # possible start times in minutes
    solver.push()                  # Save the current solver state
    solver.add(start == t)         # Try candidate start time
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()             # Restore state
        break
    solver.pop()                 # Restore state if candidate fails

if not found:
    print("No valid meeting time could be found.")