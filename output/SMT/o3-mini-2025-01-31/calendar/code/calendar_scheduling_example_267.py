from z3 import *

# Create Z3 solver instance
solver = Solver()

# Meeting parameters
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Emma's preference: avoid meetings on Monday before 13:30.
# Thus the meeting must start at or after 13:30 (i.e., 810 minutes).
solver.add(start >= 810)

# Helper function to add constraints ensuring the meeting [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bstart, bend in busy_intervals:
        # The meeting must end by the beginning of a busy interval or start after it ends.
        solver.add(Or(start + duration <= bstart, start >= bend))

# Deborah's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 14:00 to 14:30 -> [840, 870)
deborah_busy = [(540, 570), (840, 870)]
add_busy_constraints(solver, deborah_busy)

# Gary's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
gary_busy = [(750, 780), (870, 900)]
add_busy_constraints(solver, gary_busy)

# Emma's calendar is entirely open (besides her preference), so no busy intervals are needed.

# Carolyn's busy intervals:
# 9:30 to 12:00  -> [570, 720)
# 12:30 to 15:30 -> [750, 930)
# 16:00 to 16:30 -> [960, 990)
carolyn_busy = [(570, 720), (750, 930), (960, 990)]
add_busy_constraints(solver, carolyn_busy)

# Karen's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:00  -> [750, 780)
# 13:30 to 14:00  -> [810, 840)
# 15:00 to 16:30  -> [900, 990)
karen_busy = [(570, 600), (630, 660), (690, 720), (750, 780), (810, 840), (900, 990)]
add_busy_constraints(solver, karen_busy)

# Now, we search for a valid meeting start time that satisfies all constraints.
solution_found = False
for t in range(810, 1020 - duration + 1):  # t starts from 810 because of Emma's preference.
    solver.push()  # Save solver state
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