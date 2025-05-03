from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a given list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Meeting [start, start+duration) must finish before a busy interval starts or start after it ends.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Julia: No meetings (free all day) -> no constraints needed.

# Bryan's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:00 -> [660, 720)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
bryan_busy = [(600, 630), (660, 720), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, bryan_busy)

# Betty: No meetings (free all day) -> no constraints needed.

# Arthur's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 12:00 to 12:30 -> [720, 750)
arthur_busy = [(570, 600), (720, 750)]
add_busy_constraints(solver, arthur_busy)

# Megan's busy intervals:
# 9:30 to 12:00 -> [570, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 16:30 -> [930, 990)
megan_busy = [(570, 720), (750, 780), (840, 900), (930, 990)]
add_busy_constraints(solver, megan_busy)

# Kevin's busy intervals:
# 9:00 to 9:30  -> [540, 570)
# 10:00 to 11:30 -> [600, 690)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:30 -> [840, 930)
kevin_busy = [(540, 570), (600, 690), (780, 810), (840, 930)]
add_busy_constraints(solver, kevin_busy)

# Alice's busy intervals:
# 9:00 to 15:30  -> [540, 930)
# 16:00 to 16:30 -> [960, 990)
alice_busy = [(540, 930), (960, 990)]
add_busy_constraints(solver, alice_busy)

# Search for the earliest meeting time that satisfies all constraints.
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
        solver.pop()  # Remove constraints for this t value.
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")