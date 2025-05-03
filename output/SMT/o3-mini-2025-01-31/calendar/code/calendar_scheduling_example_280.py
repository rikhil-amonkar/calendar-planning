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

# Helper function: ensure the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must end before the busy period starts or begin after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Charles's busy intervals:
# 13:00 to 14:30 -> [780, 870)
# 15:00 to 16:30 -> [900, 990)
charles_busy = [(780, 870), (900, 990)]
add_busy_constraints(solver, charles_busy)

# Adam's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 16:00 to 16:30 -> [960, 990)
adam_busy = [(720, 750), (960, 990)]
add_busy_constraints(solver, adam_busy)

# Jason's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:30 to 12:00  -> [690, 720)
# 12:30 to 13:00  -> [750, 780)
# 15:00 to 15:30  -> [900, 930)
jason_busy = [(570, 600), (690, 720), (750, 780), (900, 930)]
add_busy_constraints(solver, jason_busy)

# Daniel's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 15:30 -> [840, 930)
# 16:00 to 16:30 -> [960, 990)
daniel_busy = [(570, 630), (660, 690), (750, 780), (840, 930), (960, 990)]
add_busy_constraints(solver, daniel_busy)

# Ethan's busy intervals:
# 10:00 to 12:00 -> [600, 720)
# 12:30 to 14:30 -> [750, 870)
# 16:00 to 17:00 -> [960, 1020)
ethan_busy = [(600, 720), (750, 870), (960, 1020)]
add_busy_constraints(solver, ethan_busy)

# Search for a valid meeting start time between 9:00 and 17:00.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore solver state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")