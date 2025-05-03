from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting [start, start+duration)
# does not overlap with any busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before a busy interval begins or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Joe's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 10:30 to 11:00  -> [630, 660)
joe_busy = [(570, 600), (630, 660)]
add_busy_constraints(solver, joe_busy)

# Keith's busy intervals:
# 11:30 to 12:00  -> [690, 720)
# 15:00 to 15:30  -> [900, 930)
keith_busy = [(690, 720), (900, 930)]
add_busy_constraints(solver, keith_busy)

# Patricia's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 13:00 to 13:30 -> [780, 810)
patricia_busy = [(540, 570), (780, 810)]
add_busy_constraints(solver, patricia_busy)

# Nancy's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 16:30  -> [690, 990)
nancy_busy = [(540, 660), (690, 990)]
add_busy_constraints(solver, nancy_busy)

# Pamela's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 10:30 to 11:00   -> [630, 660)
# 11:30 to 12:30   -> [690, 750)
# 13:00 to 14:00   -> [780, 840)
# 14:30 to 15:00   -> [870, 900)
# 15:30 to 16:00   -> [930, 960)
# 16:30 to 17:00   -> [990, 1020)
pamela_busy = [(540, 600), (630, 660), (690, 750), (780, 840), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, pamela_busy)

# Search for a valid meeting start time.
solution_found = False
# Iterate over all possible start times (in minutes) within [540, 1020 - duration]
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current solver state
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