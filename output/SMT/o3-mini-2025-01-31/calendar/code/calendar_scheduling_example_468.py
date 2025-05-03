from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur fully within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bstart, bend in busy_intervals:
        # Ensure the meeting [start, start+duration) either finishes before bstart,
        # or starts after bend.
        solver.add(Or(start + duration <= bstart, start >= bend))

# Stephen's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 16:00 to 17:00 -> [960, 1020)
stephen_busy = [(570, 600), (630, 660), (960, 1020)]
add_busy_constraints(solver, stephen_busy)

# Jacqueline is free all day; no constraints to add.

# Logan is free all day; no constraints to add.

# Larry's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 15:00 to 15:30 -> [900, 930)
larry_busy = [(570, 600), (900, 930)]
add_busy_constraints(solver, larry_busy)

# Jean's busy intervals:
# 9:30 to 12:00  -> [570, 720)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
jean_busy = [(570, 720), (780, 810), (840, 870), (900, 930)]
add_busy_constraints(solver, jean_busy)

# Adam's busy intervals:
# 9:00 to 12:30  -> [540, 750)
# 13:30 to 15:00 -> [810, 900)
adam_busy = [(540, 750), (810, 900)]
add_busy_constraints(solver, adam_busy)

# Eugene's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 15:30  -> [750, 930)
# 16:00 to 17:00  -> [960, 1020)
eugene_busy = [(540, 720), (750, 930), (960, 1020)]
add_busy_constraints(solver, eugene_busy)

# Search for the earliest start time that satisfies all constraints.
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