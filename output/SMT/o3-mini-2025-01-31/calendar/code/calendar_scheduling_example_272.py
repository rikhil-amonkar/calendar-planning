from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for each set of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting should finish before the busy interval starts,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Teresa's blocked times:
# 9:30 to 10:00  -> [570, 600)
# 12:00 to 13:00 -> [720, 780)
# 14:00 to 14:30 -> [840, 870)
teresa_busy = [(570, 600), (720, 780), (840, 870)]
add_busy_constraints(solver, teresa_busy)

# Scott's blocked times:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 15:00 to 16:00 -> [900, 960)
scott_busy = [(540, 570), (600, 660), (690, 720), (900, 960)]
add_busy_constraints(solver, scott_busy)

# Eric's busy times:
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:30 -> [870, 930)
eric_busy = [(720, 750), (780, 810), (870, 930)]
add_busy_constraints(solver, eric_busy)

# Maria's blocked times:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00  -> [630, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 15:30  -> [840, 930)
maria_busy = [(540, 600), (630, 720), (750, 810), (840, 930)]
add_busy_constraints(solver, maria_busy)

# Emily's blocked times:
# 9:00 to 11:30   -> [540, 690)
# 12:30 to 14:00  -> [750, 840)
# 14:30 to 15:00  -> [870, 900)
# 16:30 to 17:00  -> [990, 1020)
emily_busy = [(540, 690), (750, 840), (870, 900), (990, 1020)]
add_busy_constraints(solver, emily_busy)

# Try to find a valid meeting time by iterating over possible start times.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state in the solver.
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