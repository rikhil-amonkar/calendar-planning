from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for a list of busy intervals.
# For a busy interval [busy_start, busy_end), the meeting [start, start+duration)
# must either finish before the busy interval begins or start after it ends.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Raymond's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 11:00 to 11:30 -> [660, 690)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
raymond_busy = [(570, 600), (660, 690), (930, 960), (990, 1020)]
add_busy_constraints(solver, raymond_busy)

# Daniel's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 14:30 -> [840, 870)
daniel_busy = [(660, 690), (840, 870)]
add_busy_constraints(solver, daniel_busy)

# Julia's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 14:30 to 15:00 -> [870, 900)
julia_busy = [(780, 810), (870, 900)]
add_busy_constraints(solver, julia_busy)

# Laura's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:30 -> [600, 750)
# 15:30 to 16:30 -> [930, 990)
laura_busy = [(540, 570), (600, 750), (930, 990)]
add_busy_constraints(solver, laura_busy)

# Willie's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 12:00  -> [630, 720)
# 13:00 to 13:30  -> [780, 810)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
willie_busy = [(540, 600), (630, 720), (780, 810), (840, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, willie_busy)

# To schedule at the earliest availability, we iterate over possible start times.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}"
              .format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")