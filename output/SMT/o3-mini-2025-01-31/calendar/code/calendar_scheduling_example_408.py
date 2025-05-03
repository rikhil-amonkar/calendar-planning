from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain meeting time to be within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to avoid busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy slot, the meeting must be completely before or completely after.
        solver.add(Or(start + duration <= bs, start >= be))

# Noah is free the entire day, so no constraints needed.

# Teresa's busy intervals:
# 11:00 to 12:00 -> [660, 720)
# 14:00 to 15:00 -> [840, 900)
# 16:00 to 17:00 -> [960, 1020)
teresa_busy = [(660, 720), (840, 900), (960, 1020)]
add_busy_constraints(solver, teresa_busy)

# Bradley's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
bradley_busy = [(540, 570), (600, 630), (900, 930), (960, 990)]
add_busy_constraints(solver, bradley_busy)

# Philip's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
# 16:30 to 17:00 -> [990, 1020)
philip_busy = [(540, 570), (690, 720), (750, 780), (990, 1020)]
add_busy_constraints(solver, philip_busy)

# Joyce's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:30 to 12:30  -> [690, 750)
# 13:30 to 14:30  -> [810, 870)
# 15:30 to 17:00  -> [930, 1020)
joyce_busy = [(570, 600), (690, 750), (810, 870), (930, 1020)]
add_busy_constraints(solver, joyce_busy)

# Ryan's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 17:00 -> [840, 1020)
ryan_busy = [(540, 630), (660, 690), (840, 1020)]
add_busy_constraints(solver, ryan_busy)

# Aaron's busy intervals:
# 10:00 to 12:00 -> [600, 720)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:30 -> [900, 990)
aaron_busy = [(600, 720), (840, 870), (900, 990)]
add_busy_constraints(solver, aaron_busy)

# Search for a valid meeting time by iterating potential start times.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()           # Save the solver state.
    solver.add(start == t)  # Set candidate start time.
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()  # Restore solver state.
        break
    solver.pop()      # Restore solver state if candidate fails.

if not found:
    print("No valid meeting time could be found.")