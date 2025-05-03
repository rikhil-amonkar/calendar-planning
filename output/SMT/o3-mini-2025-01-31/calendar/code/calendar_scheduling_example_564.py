from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
duration = 30  # meeting duration in minutes (half an hour)
start = Int("start")  # meeting start time in minutes since midnight

# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Additionally, Abigail prefers no meetings after 13:30 (810 minutes),
# so we require the meeting to finish by 13:30.
solver.add(start >= 540, start + duration <= 1020, start + duration <= 810)

# Helper function to add constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))
        
# Abigail's busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 16:30 to 17:00 -> [990, 1020) (outside our window, but added for completeness)
abigail_busy = [
    (600, 630),
    (990, 1020)
]
add_busy_constraints(solver, abigail_busy)

# Matthew's busy intervals (in minutes):
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:30  -> [630, 690)
# 13:00 to 14:00  -> [780, 840)
# 15:30 to 16:30  -> [930, 990) (outside our window, but added for completeness)
matthew_busy = [
    (540, 600),
    (630, 690),
    (780, 840),
    (930, 990)
]
add_busy_constraints(solver, matthew_busy)

# Given the constraint that the meeting must finish by 13:30,
# the latest possible start time is 810 - duration = 780.
found = False
for t in range(540, 781):
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