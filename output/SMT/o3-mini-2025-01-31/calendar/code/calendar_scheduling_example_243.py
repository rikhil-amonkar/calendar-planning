from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting must finish before busy interval starts, or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Douglas has no meetings the whole day, so no busy intervals.
# Debra's busy intervals:
# 15:30 to 16:30 -> [930, 990)
debra_busy = [(930, 990)]
add_busy_constraints(solver, debra_busy)

# Frank's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
# 15:00 to 16:00 -> [900, 960)
frank_busy = [(600, 660), (720, 750), (810, 840), (900, 960)]
add_busy_constraints(solver, frank_busy)

# Nicholas's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 12:30  -> [660, 750)
# 13:30 to 15:00  -> [810, 900)
# 15:30 to 16:00  -> [930, 960)
# 16:30 to 17:00  -> [990, 1020)
nicholas_busy = [(540, 600), (660, 750), (810, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, nicholas_busy)

# Mark's busy intervals:
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:30 -> [810, 870)
# 15:00 to 17:00 -> [900, 1020)
mark_busy = [(600, 690), (720, 750), (810, 870), (900, 1020)]
add_busy_constraints(solver, mark_busy)

# Iterate over possible start times to find the earliest meeting slot that works for everyone.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_time = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_time, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")