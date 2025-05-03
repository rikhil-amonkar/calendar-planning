from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(s, busy_intervals):
    # For each busy interval [bs, be),
    # ensure the meeting either finishes before it starts or starts after it ends.
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Benjamin's busy intervals:
#   9:00 to 9:30  → [540, 570)
#   10:30 to 11:00 → [630, 660)
#   13:00 to 15:00 → [780, 900)
benjamin_busy = [(540, 570), (630, 660), (780, 900)]
add_busy_constraints(solver, benjamin_busy)

# Beverly's busy intervals:
#   10:00 to 10:30 → [600, 630)
#   12:30 to 13:00 → [750, 780)
beverly_busy = [(600, 630), (750, 780)]
add_busy_constraints(solver, beverly_busy)

# Willie's calendar is wide open, so no busy intervals.

# Ethan's busy intervals:
#   10:00 to 10:30 → [600, 630)
#   11:30 to 15:00 → [690, 900)
#   15:30 to 16:00 → [930, 960)
#   16:30 to 17:00 → [990, 1020)
ethan_busy = [(600, 630), (690, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, ethan_busy)

# Marie's busy intervals:
#   9:00 to 10:30  → [540, 630)
#   11:30 to 13:00 → [690, 780)
#   13:30 to 14:00 → [810, 840)
#   16:30 to 17:00 → [990, 1020)
marie_busy = [(540, 630), (690, 780), (810, 840), (990, 1020)]
add_busy_constraints(solver, marie_busy)

# Sandra's busy intervals:
#   9:00 to 9:30   → [540, 570)
#   10:00 to 11:30 → [600, 690)
#   12:00 to 12:30 → [720, 750)
#   13:00 to 16:00 → [780, 960)
#   16:30 to 17:00 → [990, 1020)
sandra_busy = [(540, 570), (600, 690), (720, 750), (780, 960), (990, 1020)]
add_busy_constraints(solver, sandra_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the solver state.
        break
    solver.pop()  # Restore state and continue searching.

if not found:
    print("No valid meeting time could be found.")