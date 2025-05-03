from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration is 30 minutes
start = Int("start")  # meeting start time (in minutes since midnight)

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for a participant's busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must either finish at or before b_start,
        # or start at or after b_end.
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Frank's busy intervals:
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
frank_busy = [(720, 750), (840, 870)]
add_busy_constraints(solver, frank_busy)

# Michael is free the entire day, so no constraints.

# Jeremy's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
jeremy_busy = [(630, 660), (780, 810), (870, 900), (930, 960)]
add_busy_constraints(solver, jeremy_busy)

# Charles's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
charles_busy = [(600, 630), (690, 720)]
add_busy_constraints(solver, charles_busy)

# Scott's busy intervals:
# 9:00 to 13:00  -> [540, 780)
# 13:30 to 16:30 -> [810, 990)
scott_busy = [(540, 780), (810, 990)]
add_busy_constraints(solver, scott_busy)

# Kelly's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 14:30 -> [600, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
kelly_busy = [(540, 570), (600, 870), (900, 930), (960, 990)]
add_busy_constraints(solver, kelly_busy)

# Julie's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:00 to 13:30 -> [660, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 16:30 -> [900, 990)
julie_busy = [(570, 600), (660, 810), (840, 870), (900, 990)]
add_busy_constraints(solver, julie_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert start and end times from minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")