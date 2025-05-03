from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight.

# Ensure meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Meeting must finish before busy interval starts or start after busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Donald's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 13:00 -> [690, 780)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
donald_busy = [(600, 630), (690, 780), (930, 960), (990, 1020)]
add_busy_constraints(solver, donald_busy)

# Gregory's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
gregory_busy = [(570, 600), (720, 750), (780, 810), (870, 900)]
add_busy_constraints(solver, gregory_busy)

# Roy's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 12:30 to 13:00 -> [750, 780)
roy_busy = [(600, 630), (750, 780)]
add_busy_constraints(solver, roy_busy)

# Jack's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 13:30  -> [600, 810)
# 14:00 to 16:00  -> [840, 960)
jack_busy = [(540, 570), (600, 810), (840, 960)]
add_busy_constraints(solver, jack_busy)

# Paul's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 13:30  -> [780, 810)
# 15:00 to 16:30  -> [900, 990)
paul_busy = [(540, 690), (720, 750), (780, 810), (900, 990)]
add_busy_constraints(solver, paul_busy)

# Search for a valid meeting start time between 9:00 (540) and 17:00 (1020) that satisfies all constraints.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()    # Save the state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore the state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")