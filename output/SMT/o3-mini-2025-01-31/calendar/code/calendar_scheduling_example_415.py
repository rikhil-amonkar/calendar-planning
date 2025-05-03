from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time represented in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints with a given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start + duration) must end before the busy interval or start after it.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Paul’s busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 15:00 to 15:30 -> [900, 930)
paul_busy = [(630, 660), (900, 930)]
add_busy_constraints(solver, paul_busy)

# Kyle’s busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 15:30 to 16:00 -> [930, 960)
kyle_busy = [(630, 660), (930, 960)]
add_busy_constraints(solver, kyle_busy)

# Christian’s busy intervals:
# 9:00  to 10:00  -> [540, 600)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
christian_busy = [(540, 600), (780, 810), (840, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, christian_busy)

# Alice’s busy intervals:
# 9:00  to 9:30  -> [540, 570)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 16:30 -> [930, 990)
alice_busy = [(540, 570), (720, 750), (840, 900), (930, 990)]
add_busy_constraints(solver, alice_busy)

# Kelly’s busy intervals (blocked):
# 10:30 to 15:00 -> [630, 900)
# 15:30 to 16:00 -> [930, 960)
kelly_busy = [(630, 900), (930, 960)]
add_busy_constraints(solver, kelly_busy)

# Brian’s busy intervals:
# 9:00  to 9:30   -> [540, 570)
# 10:30 to 11:30  -> [630, 690)
# 12:30 to 14:30  -> [750, 870)
# 15:00 to 16:00  -> [900, 960)
# 16:30 to 17:00  -> [990, 1020)
brian_busy = [(540, 570), (630, 690), (750, 870), (900, 960), (990, 1020)]
add_busy_constraints(solver, brian_busy)

# James’s busy intervals:
# 10:30 to 11:30 -> [630, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 17:00 -> [930, 1020)
james_busy = [(630, 690), (720, 810), (840, 900), (930, 1020)]
add_busy_constraints(solver, james_busy)

# Search for a valid meeting start time.
found = False
# Candidate start times in minutes: from 9:00 (540) to latest possible start (1020 - duration).
for t in range(540, 1020 - duration + 1):
    solver.push()          # Save the current solver state.
    solver.add(start == t) # Propose candidate start time t.
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")