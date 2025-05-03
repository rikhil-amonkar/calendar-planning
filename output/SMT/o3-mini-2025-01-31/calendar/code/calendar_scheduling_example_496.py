from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time (in minutes since midnight)

# Constrain the meeting within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Meeting [start, start+duration) must not overlap with busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Zachary's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 15:00 to 15:30 -> [900, 930)
zachary_busy = [(750, 780), (900, 930)]
add_busy_constraints(solver, zachary_busy)

# Amanda's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 12:00 to 12:30  -> [720, 750)
# 13:30 to 14:00  -> [810, 840)
amanda_busy = [(540, 600), (720, 750), (810, 840)]
add_busy_constraints(solver, amanda_busy)

# Keith's calendar is wide open (no constraints).

# Ruth's busy intervals:
# 9:30 to 10:30    -> [570, 630)
# 12:30 to 13:00   -> [750, 780)
# 16:00 to 16:30   -> [960, 990)
ruth_busy = [(570, 630), (750, 780), (960, 990)]
add_busy_constraints(solver, ruth_busy)

# Noah's busy intervals:
# 10:00 to 11:00   -> [600, 660)
# 11:30 to 12:00   -> [690, 720)
# 13:30 to 14:00   -> [810, 840)
# 15:00 to 17:00   -> [900, 1020)
noah_busy = [(600, 660), (690, 720), (810, 840), (900, 1020)]
add_busy_constraints(solver, noah_busy)

# Sean's busy intervals:
# 9:00 to 14:30   -> [540, 870)
# 15:30 to 17:00  -> [930, 1020)
sean_busy = [(540, 870), (930, 1020)]
add_busy_constraints(solver, sean_busy)

# Sara's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 13:00 to 14:30  -> [780, 870)
# 16:30 to 17:00  -> [990, 1020)
sara_busy = [(540, 660), (780, 870), (990, 1020)]
add_busy_constraints(solver, sara_busy)

# Find the earliest valid 30-minute meeting time by iterating possible start times.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")