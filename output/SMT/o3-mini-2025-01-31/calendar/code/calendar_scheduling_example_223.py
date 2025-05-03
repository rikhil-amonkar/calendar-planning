from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: For a given list of busy intervals (each as (busy_start, busy_end)),
# add constraints such that the meeting does not overlap with these intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either end before the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Frances's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   12:00 to 12:30 -> [720, 750)
#   13:30 to 14:30 -> [810, 870)
frances_busy = [(540, 570), (720, 750), (810, 870)]
add_busy_constraints(solver, frances_busy)

# Sarah's busy intervals:
#   15:00 to 15:30 -> [900, 930)
#   16:00 to 16:30 -> [960, 990)
sarah_busy = [(900, 930), (960, 990)]
add_busy_constraints(solver, sarah_busy)

# Christopher's busy intervals:
#   10:00 to 10:30 -> [600, 630)
#   13:30 to 14:00 -> [810, 840)
#   14:30 to 15:30 -> [870, 930)
christopher_busy = [(600, 630), (810, 840), (870, 930)]
add_busy_constraints(solver, christopher_busy)

# Bobby's busy intervals:
#   9:30 to 11:00  -> [570, 660)
#   12:00 to 12:30 -> [720, 750)
#   13:00 to 13:30 -> [780, 810)
#   15:00 to 16:30 -> [900, 990)
bobby_busy = [(570, 660), (720, 750), (780, 810), (900, 990)]
add_busy_constraints(solver, bobby_busy)

# Janice's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 13:30  -> [780, 810)
#   14:00 to 14:30  -> [840, 870)
#   15:30 to 16:00  -> [930, 960)
#   16:30 to 17:00  -> [990, 1020)
janice_busy = [(540, 630), (720, 750), (780, 810), (840, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, janice_busy)

# We would like to schedule the meeting at the earliest availability.
# We iterate over possible start times from 9:00 (540) to the latest possible start (1020 - 30 = 990).
solution_found = False
for t in range(540, 991):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes into HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")