from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 60 minutes
duration = 60
start = Int("start")  # Meeting start time in minutes since midnight

# Constraint: the meeting must fit entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must either end by bs or start after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Kayla's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 16:00  -> [930, 960)
kayla_busy = [(540, 600), (870, 900), (930, 960)]
add_busy_constraints(solver, kayla_busy)

# Sandra's busy intervals:
# 12:00 to 12:30  -> [720, 750)
# 14:00 to 15:00  -> [840, 900)
# 16:30 to 17:00  -> [990, 1020)
sandra_busy = [(720, 750), (840, 900), (990, 1020)]
add_busy_constraints(solver, sandra_busy)

# Ryan's busy intervals:
# 9:30 to 10:30   -> [570, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:30 to 13:00  -> [750, 780)
ryan_busy = [(570, 630), (660, 690), (750, 780)]
add_busy_constraints(solver, ryan_busy)

# Kathleen has no meetings (free all day)

# Walter's busy intervals:
# 9:30 to 12:00   -> [570, 720)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 17:00  -> [900, 1020)
walter_busy = [(570, 720), (840, 870), (900, 1020)]
add_busy_constraints(solver, walter_busy)

# Arthur's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 15:00  -> [840, 900)
arthur_busy = [(540, 660), (690, 720), (750, 780), (840, 900)]
add_busy_constraints(solver, arthur_busy)

# Heather's busy intervals:
# 10:00 to 11:30  -> [600, 690)
# 12:00 to 13:00  -> [720, 780)
# 14:30 to 15:30  -> [870, 930)
# 16:30 to 17:00  -> [990, 1020)
heather_busy = [(600, 690), (720, 780), (870, 930), (990, 1020)]
add_busy_constraints(solver, heather_busy)

# Now, iterate minute-by-minute over possible start times to find a valid meeting slot.
found = False
# The end of the time range is 1020 - duration + 1 because meeting must finish by 1020.
for t in range(540, 1020 - duration + 1):
    solver.push()           # Save the state.
    solver.add(start == t)  # Set the candidate start time.
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore the state.
        break
    solver.pop()      # Restore state if candidate not valid.

if not found:
    print("No valid meeting time could be found.")