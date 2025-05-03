from z3 import Solver, Int, Or, sat

# Initialize the Z3 solver.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 min) to 17:00 (1020 min)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Ronald's preference: he would like to avoid meetings after 11:00.
# We enforce that the meeting must finish by 11:00 (i.e. 660 minutes).
solver.add(start + duration <= 660)

# Helper function to add constraints for a participant's busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) must either end by the busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jack's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 15:00 -> [840, 900)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
jack_busy = [(570, 600), (780, 810), (840, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, jack_busy)

# Frank's busy intervals:
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
# (None of these fall before 11:00, so they don't affect our domain.)
frank_busy = [(750, 780), (810, 840)]
add_busy_constraints(solver, frank_busy)

# Theresa: free all day (no busy intervals).

# Ronald: free all day aside from his meeting time preference (already added).

# Alexander's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:30 -> [690, 750)
# 13:00 to 13:30 -> [780, 810)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
alexander_busy = [(570, 600), (630, 660), (690, 750), (780, 810), (900, 930), (960, 1020)]
add_busy_constraints(solver, alexander_busy)

# Peter's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 15:00 -> [810, 900)
# 16:00 to 17:00 -> [960, 1020)
peter_busy = [(570, 600), (720, 780), (810, 900), (960, 1020)]
add_busy_constraints(solver, peter_busy)

# Anthony's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 11:30 to 13:00 -> [690, 780)
# 13:30 to 15:00 -> [810, 900)
# 16:00 to 16:30 -> [960, 990)
anthony_busy = [(570, 600), (690, 780), (810, 900), (960, 990)]
add_busy_constraints(solver, anthony_busy)

# We now search for a valid meeting start time.
found = False
# Considering Ronald's preference, meeting must finish by 11:00,
# so valid start times are between 9:00 (540) and 11:00-30 (630) inclusive.
for t in range(540, 630 + 1):
    solver.push()        # Save the current solver state.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")