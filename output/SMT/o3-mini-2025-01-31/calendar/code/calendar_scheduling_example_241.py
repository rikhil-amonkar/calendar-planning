from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Adam would like to avoid meetings before 10:30.
# Enforce that the meeting starts no earlier than 10:30 (630 minutes).
solver.add(start >= 630)

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any busy interval provided.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish at or before the busy interval starts,
        # or start at or after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Terry's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 16:30 to 17:00 -> [990, 1020)
terry_busy = [(810, 840), (990, 1020)]
add_busy_constraints(solver, terry_busy)

# Janet's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:30 to 17:00 -> [990, 1020)
janet_busy = [(570, 600), (750, 780), (810, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, janet_busy)

# Lauren has no meetings the whole day: no busy intervals.

# Sharon's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 17:00 -> [750, 1020)
sharon_busy = [(570, 630), (690, 720), (750, 1020)]
add_busy_constraints(solver, sharon_busy)

# Adam's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 17:00 -> [660, 1020)
adam_busy = [(570, 630), (660, 1020)]
add_busy_constraints(solver, adam_busy)

# Since we want the group's earliest available time,
# iterate from 10:30 (630) (because of Adam's constraint) up to the latest start time.
solution_found = False
for t in range(630, 1020 - duration + 1):
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