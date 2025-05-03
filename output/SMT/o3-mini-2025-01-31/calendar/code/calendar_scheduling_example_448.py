from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: given a list of busy time intervals (each as (start, end) in minutes),
# ensure that the meeting [start, start+duration) does not overlap with any interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Thomas' busy intervals:
#   9:00 to 9:30 -> [540, 570)
#   11:30 to 12:30 -> [690, 750)
#   16:30 to 17:00 -> [990, 1020)
thomas_busy = [(540, 570), (690, 750), (990, 1020)]
add_busy_constraints(solver, thomas_busy)

# Kyle's busy intervals:
#   9:00 to 9:30 -> [540, 570)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 13:30 -> [780, 810)
#   14:30 to 15:30 -> [870, 930)
#   16:00 to 16:30 -> [960, 990)
kyle_busy = [(540, 570), (720, 750), (780, 810), (870, 930), (960, 990)]
add_busy_constraints(solver, kyle_busy)

# Helen's calendar is wide open; no constraints needed.

# Anna's busy intervals:
#   12:00 to 12:30 -> [720,750)
#   14:30 to 15:00 -> [870,900)
anna_busy = [(720, 750), (870, 900)]
add_busy_constraints(solver, anna_busy)

# Lauren's busy intervals:
#   9:00 to 10:00 -> [540,600)
#   10:30 to 11:00 -> [630,660)
#   11:30 to 12:00 -> [690,720)
#   13:00 to 13:30 -> [780,810)
#   14:00 to 16:00 -> [840,960)
#   16:30 to 17:00 -> [990,1020)
lauren_busy = [(540,600), (630,660), (690,720), (780,810), (840,960), (990,1020)]
add_busy_constraints(solver, lauren_busy)

# Frances' busy interval:
#   11:00 to 17:00 -> [660,1020)
frances_busy = [(660, 1020)]
add_busy_constraints(solver, frances_busy)

# Maria's busy intervals:
#   9:00 to 10:00   -> [540,600)
#   12:00 to 12:30  -> [720,750)
#   13:00 to 14:00  -> [780,840)
#   15:00 to 16:00  -> [900,960)
#   16:30 to 17:00  -> [990,1020)
maria_busy = [(540,600), (720,750), (780,840), (900,960), (990,1020)]
add_busy_constraints(solver, maria_busy)

# Iterate over possible meeting start times (each minute within work hours)
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}."
              .format(start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")