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

# Helper function to add non-overlap constraints for a participant's busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval starts
        # or begin after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Megan's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 15:30 to 16:00 -> [930, 960)
megan_busy = [(720, 750), (930, 960)]
add_busy_constraints(solver, megan_busy)

# Jacob is free the whole day; no busy intervals.

# Kathryn is free the whole day; no busy intervals.

# Keith's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:30 to 15:30  -> [810, 930)
# 16:00 to 17:00  -> [960, 1020)
keith_busy = [(540, 660), (690, 750), (810, 930), (960, 1020)]
add_busy_constraints(solver, keith_busy)

# Matthew's busy intervals:
# 9:30 to 11:30   -> [570, 690)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:00  -> [810, 840)
# 14:30 to 15:30  -> [870, 930)
matthew_busy = [(570, 690), (750, 780), (810, 840), (870, 930)]
add_busy_constraints(solver, matthew_busy)

# Search for the earliest valid meeting time satisfying all constraints.
solution_found = False
# The latest valid start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save the current state.
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