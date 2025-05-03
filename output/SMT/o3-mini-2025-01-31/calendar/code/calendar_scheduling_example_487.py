from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# A helper function to add busy-time constraints for each participant.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # To avoid overlapping with a busy interval [b_start, b_end),
        # the meeting must finish before b_start or start after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant Schedules:

# Albert: Free the entire day, no constraints needed.

# Rebecca's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
rebecca_busy = [(780, 810), (840, 870)]
add_busy_constraints(solver, rebecca_busy)

# Ronald's busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 12:30 -> [720, 750)
# 15:00 to 15:30 -> [900, 930)
ronald_busy = [(630, 690), (720, 750), (900, 930)]
add_busy_constraints(solver, ronald_busy)

# Pamela's busy intervals:
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 16:30 -> [960, 990)
pamela_busy = [(810, 840), (960, 990)]
add_busy_constraints(solver, pamela_busy)

# Noah's busy intervals:
# 9:30 to 11:00   -> [570, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 15:30  -> [900, 930)
# 16:00 to 17:00  -> [960, 1020)
noah_busy = [(570, 660), (690, 750), (780, 810), (840, 870), (900, 930), (960, 1020)]
add_busy_constraints(solver, noah_busy)

# Diana's busy intervals:
# 9:00 to 13:00   -> [540, 780)
# 13:30 to 15:30  -> [810, 930)
# 16:00 to 17:00  -> [960, 1020)
diana_busy = [(540, 780), (810, 930), (960, 1020)]
add_busy_constraints(solver, diana_busy)

# Jacqueline's busy intervals:
# 9:30 to 12:00   -> [570, 720)
# 13:00 to 15:00  -> [780, 900)
# 16:00 to 16:30  -> [960, 990)
jacqueline_busy = [(570, 720), (780, 900), (960, 990)]
add_busy_constraints(solver, jacqueline_busy)

# Find the earliest valid meeting time by iterating through potential start times.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert the meeting start and end times to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")