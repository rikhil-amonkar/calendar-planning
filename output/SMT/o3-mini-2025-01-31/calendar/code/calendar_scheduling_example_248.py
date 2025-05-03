from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting occurs within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to ensure the meeting interval [start, start+duration)
# does not overlap with any given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end before a busy interval starts, or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Billy's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 16:30 -> [870, 990)
billy_busy = [(600, 630), (690, 720), (870, 990)]
add_busy_constraints(solver, billy_busy)

# Joe's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
joe_busy = [(570, 600), (690, 720)]
add_busy_constraints(solver, joe_busy)

# Brittany's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 16:00 -> [930, 960)
brittany_busy = [(810, 840), (930, 960)]
add_busy_constraints(solver, brittany_busy)

# Grace's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:30 to 16:30 -> [810, 990)
grace_busy = [(570, 600), (630, 660), (690, 750), (810, 990)]
add_busy_constraints(solver, grace_busy)

# Dennis's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 17:00 -> [930, 1020)
dennis_busy = [(570, 630), (660, 720), (750, 780), (810, 840), (870, 900), (930, 1020)]
add_busy_constraints(solver, dennis_busy)

# We want the earliest meeting time that works for everyone.
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