from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 60 minutes.
duration = 60
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(s, busy_intervals):
    # For each busy interval [bs, be),
    # the meeting must either finish before bs or start after the busy interval ends.
    for bs, be in busy_intervals:
        s.add(Or(start + duration <= bs, start >= be))

# Ryan's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   16:00 to 16:30 -> [960, 990)
ryan_busy = [(600, 630), (960, 990)]
add_busy_constraints(solver, ryan_busy)

# Brandon is free all day, so no constraints are added.

# Sandra's busy intervals:
#   11:00 to 11:30 -> [660, 690)
#   15:30 to 16:00 -> [930, 960)
sandra_busy = [(660, 690), (930, 960)]
add_busy_constraints(solver, sandra_busy)

# Jonathan's busy intervals:
#   9:00 to 12:00   -> [540, 720)
#   12:30 to 13:00  -> [750, 780)
#   14:00 to 16:30  -> [840, 990)
jonathan_busy = [(540, 720), (750, 780), (840, 990)]
add_busy_constraints(solver, jonathan_busy)

# Elijah's busy intervals:
#   9:30 to 11:00   -> [570, 660)
#   12:00 to 13:00  -> [720, 780)
#   14:00 to 16:30  -> [840, 990)
elijah_busy = [(570, 660), (720, 780), (840, 990)]
add_busy_constraints(solver, elijah_busy)

# Justin's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   11:30 to 13:00  -> [690, 780)
#   14:30 to 16:30  -> [870, 990)
justin_busy = [(540, 630), (690, 780), (870, 990)]
add_busy_constraints(solver, justin_busy)

# Search for the earliest valid meeting time.
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
        solver.pop()  # Restore the solver state.
        break
    solver.pop()  # Restore state and try the next potential start time.

if not found:
    print("No valid meeting time could be found.")