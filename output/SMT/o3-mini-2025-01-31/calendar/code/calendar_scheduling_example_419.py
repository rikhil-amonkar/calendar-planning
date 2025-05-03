from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) doesn't overlap the busy interval.
        # Either the meeting finishes before the busy interval starts, or it starts after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Shirley is free all day, so no constraints.

# Mary is busy from 16:00 to 17:00 => [960, 1020)
mary_busy = [(960, 1020)]
add_busy_constraints(solver, mary_busy)

# Doris is busy from:
# 10:30 to 11:30 => [630, 690)
# 12:00 to 12:30 => [720, 750)
# 15:00 to 16:30 => [900, 990)
doris_busy = [(630, 690), (720, 750), (900, 990)]
add_busy_constraints(solver, doris_busy)

# Daniel is busy from:
# 9:00 to 9:30   => [540,570)
# 10:00 to 11:30 => [600,690)
# 12:00 to 12:30 => [720,750)
# 16:00 to 16:30 => [960,990)
daniel_busy = [(540, 570), (600, 690), (720, 750), (960, 990)]
add_busy_constraints(solver, daniel_busy)

# Madison is busy from:
# 9:00 to 9:30    => [540,570)
# 10:00 to 12:30  => [600,750)
# 13:00 to 13:30  => [780,810)
# 14:30 to 15:00  => [870,900)
# 15:30 to 16:00  => [930,960)
# 16:30 to 17:00  => [990,1020)
madison_busy = [(540, 570), (600, 750), (780, 810), (870, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, madison_busy)

# Albert is busy from:
# 10:00 to 11:00   => [600,660)
# 11:30 to 12:00   => [690,720)
# 12:30 to 13:00   => [750,780)
# 14:30 to 15:00   => [870,900)
# 15:30 to 17:00   => [930,1020)
albert_busy = [(600, 660), (690, 720), (750, 780), (870, 900), (930, 1020)]
add_busy_constraints(solver, albert_busy)

# Stephanie is busy from:
# 9:30 to 11:30   => [570,690)
# 12:00 to 12:30  => [720,750)
# 13:00 to 13:30  => [780,810)
# 14:00 to 15:00  => [840,900)
stephanie_busy = [(570, 690), (720, 750), (780, 810), (840, 900)]
add_busy_constraints(solver, stephanie_busy)

# Now, iterate over possible start times to find one slot that works for everyone.
found = False
for t in range(540, 1020 - duration + 1):
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