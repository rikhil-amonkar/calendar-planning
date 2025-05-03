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

# Wayne's preference: He would like to avoid more meetings before 16:00.
# This implies he prefers meetings scheduled at or after 16:00 (i.e. 960 minutes),
# so we add that as a constraint.
solver.add(start >= 960)

# Helper function to add non-overlap constraints for each busy interval.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # ensure the meeting interval [start, start+duration)
    # either ends on or before busy_start or starts on or after busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Keith's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 12:00 -> [630, 720)
# 12:30 to 13:30 -> [750, 810)
keith_busy = [(540, 570), (630, 720), (750, 810)]
add_busy_constraints(solver, keith_busy)

# Wayne's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:30 to 11:00  -> [630, 660)
# 14:30 to 15:00  -> [870, 900)
# 16:00 to 16:30  -> [960, 990)
wayne_busy = [(540, 570), (630, 660), (870, 900), (960, 990)]
add_busy_constraints(solver, wayne_busy)

# Harold's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 10:30 to 11:00  -> [630, 660)
# 11:30 to 12:30  -> [690, 750)
# 13:00 to 14:00  -> [780, 840)
# 15:00 to 15:30  -> [900, 930)
harold_busy = [(540, 600), (630, 660), (690, 750), (780, 840), (900, 930)]
add_busy_constraints(solver, harold_busy)

# Ralph's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:30 to 15:30  -> [630, 930)
# 16:00 to 16:30  -> [960, 990)
ralph_busy = [(540, 570), (630, 930), (960, 990)]
add_busy_constraints(solver, ralph_busy)

# Search for a valid start time.
solution_found = False
# The latest possible start time is 1020 - 30 = 990.
# Also, given Wayne's preference, we start checking from 960.
for t in range(960, 991):
    solver.push()  # Save the current state.
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
        solver.pop()  # Restore the state.
        break
    solver.pop()  # Restore the state if unsat.

if not solution_found:
    print("No valid meeting time could be found.")