from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
# For each busy interval [busy_start, busy_end), the meeting [start, start+duration)
# must either end on-or-before busy_start or begin on-or-after busy_end.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jesse's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 15:00 to 15:30 -> [900, 930)
jesse_busy = [(600, 630), (900, 930)]
add_busy_constraints(solver, jesse_busy)

# Nancy's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
nancy_busy = [(540, 570), (630, 660), (810, 840), (870, 900)]
add_busy_constraints(solver, nancy_busy)

# Isabella's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:30 to 12:00  -> [690, 720)
# 15:30 to 16:00  -> [930, 960)
isabella_busy = [(540, 600), (690, 720), (930, 960)]
add_busy_constraints(solver, isabella_busy)

# Harold's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 10:30 to 16:30   -> [630, 990)
harold_busy = [(540, 600), (630, 990)]
add_busy_constraints(solver, harold_busy)

# Linda's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 16:00  -> [810, 960)
linda_busy = [(540, 600), (720, 750), (810, 960)]
add_busy_constraints(solver, linda_busy)

# To schedule at the earliest availability, we iterate over possible start times.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")