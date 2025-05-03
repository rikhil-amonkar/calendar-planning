from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time, in minutes since midnight

# Ensure the meeting is scheduled within the work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for a participant's busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting must either finish before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Nicholas's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
# 15:30 to 16:00 -> [930, 960)
nicholas_busy = [(540, 570), (660, 690), (750, 780), (930, 960)]
add_busy_constraints(solver, nicholas_busy)

# Sara's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
sara_busy = [(600, 630), (660, 690)]
add_busy_constraints(solver, sara_busy)

# Helen is free the entire day, so no constraints needed.
# Brian is free the entire day, so no constraints needed.

# Nancy's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 14:00  -> [660, 840)
# 15:00 to 17:00  -> [900, 1020)
nancy_busy = [(540, 600), (660, 840), (900, 1020)]
add_busy_constraints(solver, nancy_busy)

# Kelly's busy intervals:
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:30 to 17:00 -> [990, 1020)
kelly_busy = [(600, 690), (720, 750), (810, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, kelly_busy)

# Judy's busy intervals:
# 9:00 to 11:30   -> [540, 690)
# 12:00 to 12:30  -> [720, 750)
# 13:00 to 13:30  -> [780, 810)
# 14:30 to 17:00  -> [870, 1020)
judy_busy = [(540, 690), (720, 750), (780, 810), (870, 1020)]
add_busy_constraints(solver, judy_busy)

# Try to find the earliest valid meeting time.
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