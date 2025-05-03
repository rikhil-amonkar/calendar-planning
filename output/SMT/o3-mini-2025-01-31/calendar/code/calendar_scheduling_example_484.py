from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# The meeting must be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for a participant's busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either end before b_start
        # or start after b_end, so that it doesn't overlap the busy interval.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Jean's blocked times:
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:30 -> [930, 990)
jean_busy = [(720, 750), (840, 870), (930, 990)]
add_busy_constraints(solver, jean_busy)

# Susan is free the entire day, no constraints needed.
# Beverly is free the entire day, no constraints needed.

# Denise's meetings:
# 9:30 to 11:00   -> [570, 660)
# 12:30 to 13:00  -> [750, 780)
# 15:00 to 15:30  -> [900, 930)
# 16:30 to 17:00  -> [990, 1020)
denise_busy = [(570, 660), (750, 780), (900, 930), (990, 1020)]
add_busy_constraints(solver, denise_busy)

# Jeffrey's busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 14:30 to 16:30  -> [870, 990)
jeffrey_busy = [(540, 720), (870, 990)]
add_busy_constraints(solver, jeffrey_busy)

# Mary's blocked times:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 13:00 -> [660, 780)
# 13:30 to 14:30 -> [810, 870)
mary_busy = [(540, 570), (600, 630), (660, 780), (810, 870)]
add_busy_constraints(solver, mary_busy)

# Joseph's meetings:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 13:00  -> [630, 780)
# 13:30 to 15:00  -> [810, 900)
# 15:30 to 16:30  -> [930, 990)
joseph_busy = [(540, 600), (630, 780), (810, 900), (930, 990)]
add_busy_constraints(solver, joseph_busy)

# Find the earliest valid meeting time.
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