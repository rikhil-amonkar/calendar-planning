from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 = 540, 17:00 = 1020, meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time, in minutes since midnight

# Jason doesn't want to meet before 10:30, so we set a lower bound of 10:30 (630 minutes)
solver.add(start >= 630, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting must either finish by the start of the busy interval,
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= bs, start >= be))

# Bryan's busy intervals:
#   9:30 to 10:00 -> [570, 600)
#   13:30 to 14:30 -> [810, 870)
#   15:00 to 16:30 -> [900, 990)
bryan_busy = [(570, 600), (810, 870), (900, 990)]
add_busy_constraints(solver, bryan_busy)

# Benjamin is free all day, so no constraints.

# Matthew's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 12:00 -> [630, 720)
#   14:00 to 14:30 -> [840, 870)
#   15:30 to 16:00 -> [930, 960)
matthew_busy = [(540, 570), (630, 720), (840, 870), (930, 960)]
add_busy_constraints(solver, matthew_busy)

# Margaret's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 12:00 -> [630, 720)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 14:30 -> [810, 870)
#   15:00 to 15:30 -> [900, 930)
margaret_busy = [(540, 570), (630, 720), (750, 780), (810, 870), (900, 930)]
add_busy_constraints(solver, margaret_busy)

# Donald's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 13:30  -> [630, 810)
#   14:00 to 14:30  -> [840, 870)
#   15:30 to 17:00  -> [930, 1020)
donald_busy = [(540, 600), (630, 810), (840, 870), (930, 1020)]
add_busy_constraints(solver, donald_busy)

# Jason's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 13:30  -> [780, 810)
#   15:00 to 17:00  -> [900, 1020)
jason_busy = [(540, 600), (720, 750), (780, 810), (900, 1020)]
add_busy_constraints(solver, jason_busy)

# Search for the earliest meeting time that satisfies all constraints.
found = False
for t in range(630, 1020 - duration + 1):  # t from 10:30 (630) onward
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")