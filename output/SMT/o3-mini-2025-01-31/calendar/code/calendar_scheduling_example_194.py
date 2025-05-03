from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for each busy interval.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # the meeting interval [start, start+duration) must either end at or before busy_start
    # or start at or after busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Dennis's busy intervals:
# 9:30-10:30 -> [570, 630)
# 11:30-12:00 -> [690, 720)
# 13:30-14:00 -> [810, 840)
# 14:30-15:00 -> [870, 900)
# 15:30-16:00 -> [930, 960)
dennis_busy = [(570, 630), (690, 720), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, dennis_busy)

# Victoria's busy intervals:
# 9:00-9:30 -> [540, 570)
# 10:30-11:00 -> [630, 660)
# 11:30-12:00 -> [690, 720)
# 12:30-13:00 -> [750, 780)
# 14:30-15:30 -> [870, 930)
victoria_busy = [(540, 570), (630, 660), (690, 720), (750, 780), (870, 930)]
add_busy_constraints(solver, victoria_busy)

# Samantha's busy intervals:
# 9:00-10:00 -> [540, 600)
# 10:30-11:00 -> [630, 660)
# 11:30-12:30 -> [690, 750)
# 13:00-14:00 -> [780, 840)
# 14:30-15:00 -> [870, 900)
# 16:00-17:00 -> [960, 1020)
samantha_busy = [(540, 600), (630, 660), (690, 750), (780, 840), (870, 900), (960, 1020)]
add_busy_constraints(solver, samantha_busy)

# Jeffrey's busy intervals:
# 9:00-9:30 -> [540, 570)
# 10:30-11:00 -> [630, 660)
# 11:30-13:00 -> [690, 780)
# 13:30-15:00 -> [810, 900)
# 15:30-16:00 -> [930, 960)
# 16:30-17:00 -> [990, 1020)
jeffrey_busy = [(540, 570), (630, 660), (690, 780), (810, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, jeffrey_busy)

# Search for a valid start time.
solution_found = False
# The latest possible start time is 1020 - 30 = 990.
for t in range(540, 991):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")