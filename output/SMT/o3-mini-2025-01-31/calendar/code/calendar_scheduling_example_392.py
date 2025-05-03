from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 (540) to 17:00 (1020)
# and the meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is entirely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either end before the busy interval starts or start after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Donald's busy intervals:
#   11:30 to 12:30 -> [690, 750)
#   14:00 to 14:30 -> [840, 870)
#   15:30 to 16:00 -> [930, 960)
donald_busy = [(690, 750), (840, 870), (930, 960)]
add_busy_constraints(solver, donald_busy)

# Alice's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   13:00 to 14:00 -> [780, 840)
#   15:00 to 16:00 -> [900, 960)
#   16:30 to 17:00 -> [990, 1020)
alice_busy = [(630, 660), (780, 840), (900, 960), (990, 1020)]
add_busy_constraints(solver, alice_busy)

# Doris's busy intervals:
#   10:30 to 11:00 -> [630, 660)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 14:00 -> [780, 840)
#   16:00 to 17:00 -> [960, 1020)
doris_busy = [(630, 660), (720, 750), (780, 840), (960, 1020)]
add_busy_constraints(solver, doris_busy)

# Jesse's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 14:00 -> [780, 840)
#   15:00 to 15:30 -> [900, 930)
#   16:30 to 17:00 -> [990, 1020)
jesse_busy = [(540, 570), (600, 660), (720, 750), (780, 840), (900, 930), (990, 1020)]
add_busy_constraints(solver, jesse_busy)

# Noah's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   11:30 to 13:00  -> [690, 780)
#   13:30 to 17:00  -> [810, 1020)
noah_busy = [(540, 660), (690, 780), (810, 1020)]
add_busy_constraints(solver, noah_busy)

# Jerry's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   12:00 to 12:30 -> [720, 750)
#   14:30 to 15:00 -> [870, 900)
#   15:30 to 17:00 -> [930, 1020)
jerry_busy = [(540, 570), (600, 660), (720, 750), (870, 900), (930, 1020)]
add_busy_constraints(solver, jerry_busy)

# Iterate minute by minute to find the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()   # Restore state
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")