from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either finish before a busy interval starts 
        # or start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Define busy intervals for each participant, in minutes from midnight.

# Gregory's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 11:30 to 12:00 -> [690, 720)
gregory_busy = [(540, 570), (690, 720)]
add_busy_constraints(solver, gregory_busy)

# Jonathan's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 12:00 to 12:30 -> [720, 750)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 16:00 -> [900, 960)
# 16:30 to 17:00 -> [990, 1020)
jonathan_busy = [(540, 570), (720, 750), (780, 810), (900, 960), (990, 1020)]
add_busy_constraints(solver, jonathan_busy)

# Barbara's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 13:30 to 14:00 -> [810, 840)
barbara_busy = [(600, 630), (810, 840)]
add_busy_constraints(solver, barbara_busy)

# Jesse's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 12:30 to 14:30 -> [750, 870)
jesse_busy = [(600, 660), (750, 870)]
add_busy_constraints(solver, jesse_busy)

# Alan's busy intervals:
# 9:30 to 11:00 -> [570, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 15:30 -> [780, 930)
# 16:00 to 17:00 -> [960, 1020)
alan_busy = [(570, 660), (690, 750), (780, 930), (960, 1020)]
add_busy_constraints(solver, alan_busy)

# Nicole's busy intervals:
# 9:00 to 10:30 -> [540, 630)
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:30 -> [750, 810)
# 14:00 to 17:00 -> [840, 1020)
nicole_busy = [(540, 630), (690, 720), (750, 810), (840, 1020)]
add_busy_constraints(solver, nicole_busy)

# Catherine's busy intervals:
# 9:00 to 10:30 -> [540, 630)
# 12:00 to 13:30 -> [720, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 16:30 -> [960, 990)
catherine_busy = [(540, 630), (720, 810), (900, 930), (960, 990)]
add_busy_constraints(solver, catherine_busy)

# Search for the earliest available meeting time that fits everyone's schedule.
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