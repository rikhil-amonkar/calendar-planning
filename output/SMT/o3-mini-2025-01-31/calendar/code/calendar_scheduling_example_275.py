from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Constrain meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints to avoid overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must end before a busy interval starts, or begin after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jose's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
jose_busy = [(660, 690), (750, 780)]
add_busy_constraints(solver, jose_busy)

# Albert's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 14:30 -> [780, 870)
# 15:00 to 15:30 -> [900, 930)
albert_busy = [(600, 630), (660, 690), (780, 870), (900, 930)]
add_busy_constraints(solver, albert_busy)

# Brenda's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:30 -> [930, 990)
brenda_busy = [(600, 630), (660, 690), (780, 810), (870, 900), (930, 990)]
add_busy_constraints(solver, brenda_busy)

# Bruce's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 13:00 -> [630, 780)
# 13:30 to 16:30 -> [810, 990)
bruce_busy = [(570, 600), (630, 780), (810, 990)]
add_busy_constraints(solver, bruce_busy)

# Jacob's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 14:00 -> [720, 840)
# 15:00 to 15:30 -> [900, 930)
jacob_busy = [(540, 570), (630, 690), (720, 840), (900, 930)]
add_busy_constraints(solver, jacob_busy)

# Search for a valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")