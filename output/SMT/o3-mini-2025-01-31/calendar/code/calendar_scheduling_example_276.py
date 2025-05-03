from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# However, Willie cannot meet after 12:00, so the meeting must end by 12:00 (720 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# The meeting must be within work hours and must end by 12:00 (due to Willie's constraint).
solver.add(start >= 540, start + duration <= 1020, start + duration <= 720)

# Helper function to add constraints to ensure the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either end before the busy interval starts or begin after it ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Christine's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
christine_busy = [(570, 600), (630, 660), (720, 750), (780, 810)]
add_busy_constraints(solver, christine_busy)

# Natalie's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 13:00 to 13:30 -> [780, 810)
# 16:00 to 16:30 -> [960, 990)
natalie_busy = [(600, 630), (660, 690), (780, 810), (960, 990)]
add_busy_constraints(solver, natalie_busy)

# Willie is free throughout the day,
# but he cannot meet after 12:00 (already enforced by start + duration <= 720).

# Anna's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 11:00 to 13:30  -> [660, 810)
# 14:30 to 15:00  -> [870, 900)
# 15:30 to 17:00  -> [930, 1020)
anna_busy = [(570, 600), (660, 810), (870, 900), (930, 1020)]
add_busy_constraints(solver, anna_busy)

# Evelyn's busy intervals:
# 11:00 to 12:00  -> [660, 720)
# 12:30 to 13:30  -> [750, 810)
# 14:00 to 15:00  -> [840, 900)
# 16:00 to 17:00  -> [960, 1020)
evelyn_busy = [(660, 720), (750, 810), (840, 900), (960, 1020)]
add_busy_constraints(solver, evelyn_busy)

# Since Willie cannot meet after 12:00, the valid range of meeting start times is from 9:00 to 11:30 (i.e. 540 to 690).
# We search for a valid meeting start time within this interval.
solution_found = False
for t in range(540, 691):  # t from 540 to 690 inclusive, ensuring meeting ends by 720.
    solver.push()  # Save current state.
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