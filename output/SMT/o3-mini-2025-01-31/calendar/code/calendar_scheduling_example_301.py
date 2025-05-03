from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes past midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting does not overlap a busy interval.
def add_busy_constraints(s, busy_intervals):
    for bs, be in busy_intervals:
        # The meeting can be scheduled so that it ends before the busy interval starts,
        # or begins after or when the busy interval ends.
        s.add(Or(start + duration <= bs, start >= be))

# Amy's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 15:30 to 16:00 -> [930, 960)
amy_busy = [(780, 810), (930, 960)]
add_busy_constraints(solver, amy_busy)

# Jonathan's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
jonathan_busy = [(540, 570), (600, 630), (690, 720), (750, 780)]
add_busy_constraints(solver, jonathan_busy)

# Brittany's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 16:30 to 17:00 -> [990, 1020)
brittany_busy = [(570, 600), (990, 1020)]
add_busy_constraints(solver, brittany_busy)

# Matthew's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 12:30 to 14:30  -> [750, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 16:30  -> [960, 990)
matthew_busy = [(540, 600), (750, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, matthew_busy)

# Catherine's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 12:00 to 14:00  -> [720, 840)
# 16:30 to 17:00  -> [990, 1020)
catherine_busy = [(540, 630), (720, 840), (990, 1020)]
add_busy_constraints(solver, catherine_busy)

# Carl's busy intervals:
# 10:00 to 11:00   -> [600, 660)
# 11:30 to 12:30   -> [690, 750)
# 13:00 to 14:00   -> [780, 840)
# 14:30 to 16:30   -> [870, 990)
carl_busy = [(600, 660), (690, 750), (780, 840), (870, 990)]
add_busy_constraints(solver, carl_busy)

# Find the earliest valid meeting start time that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minute-based times to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")