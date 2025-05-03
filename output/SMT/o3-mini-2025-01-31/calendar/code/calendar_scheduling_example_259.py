from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes since midnight) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint:
# Randy does not want the meeting after 15:30.
# We interpret this as the meeting must finish by 15:30 (i.e., start + duration ≤ 930).
solver.add(start + duration <= 930)

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either end before a busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Randy's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
# 16:00 to 17:00 -> [960, 1020)
randy_busy = [(660, 690), (750, 780), (960, 1020)]
add_busy_constraints(solver, randy_busy)

# Carolyn's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 11:30  -> [660, 690)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 16:30  -> [960, 990)
carolyn_busy = [(570, 600), (660, 690), (900, 930), (960, 990)]
add_busy_constraints(solver, carolyn_busy)

# Christina's busy intervals:
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 14:00  -> [810, 840)
christina_busy = [(720, 750), (810, 840)]
add_busy_constraints(solver, christina_busy)

# Amy's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 15:30  -> [810, 930)
# 16:00 to 17:00  -> [960, 1020)
amy_busy = [(540, 690), (720, 750), (810, 930), (960, 1020)]
add_busy_constraints(solver, amy_busy)

# Christine's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
christine_busy = [(540, 630), (660, 690), (720, 780), (840, 870), (960, 990)]
add_busy_constraints(solver, christine_busy)

# Search for the earliest valid meeting start time.
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