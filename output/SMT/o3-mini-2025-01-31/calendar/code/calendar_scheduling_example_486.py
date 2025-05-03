from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper to add busy time constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either end at or before b_start,
        # or start at or after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Logan's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:30 to 12:00 -> [690, 720)
logan_busy = [(570, 600), (690, 720)]
add_busy_constraints(solver, logan_busy)

# Kimberly's busy intervals:
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
kimberly_busy = [(840, 870), (960, 990)]
add_busy_constraints(solver, kimberly_busy)

# Angela's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
angela_busy = [(600, 630), (780, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, angela_busy)

# Matthew is free the entire day, so no constraints are added.

# Dylan's busy intervals:
# 9:30 to 12:00  -> [570, 720)
# 13:00 to 14:00 -> [780, 840)
# 15:30 to 16:00 -> [930, 960)
dylan_busy = [(570, 720), (780, 840), (930, 960)]
add_busy_constraints(solver, dylan_busy)

# Marilyn's busy intervals:
# 9:00 to 11:00   -> [540, 660)
# 11:30 to 14:30  -> [690, 870)
# 15:00 to 17:00  -> [900, 1020)
marilyn_busy = [(540, 660), (690, 870), (900, 1020)]
add_busy_constraints(solver, marilyn_busy)

# Grace's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 14:00 -> [780, 840)
# 15:30 to 17:00 -> [930, 1020)
grace_busy = [(540, 570), (600, 660), (690, 750), (780, 840), (930, 1020)]
add_busy_constraints(solver, grace_busy)

# Find the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")