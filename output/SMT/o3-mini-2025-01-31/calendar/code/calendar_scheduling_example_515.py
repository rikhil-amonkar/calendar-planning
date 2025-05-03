from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 60  # meeting duration is 60 minutes (1 hour)
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Dylan would like to avoid meetings on Monday before 16:00.
# Therefore, the meeting must start at or after 16:00 (960 minutes).
solver.add(start >= 960)

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting interval [start, start+duration) must not overlap with the busy interval [b_start, b_end)
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Randy's busy intervals (in minutes):
# 10:00 to 10:30 -> [600, 630)
# 15:00 to 15:30 -> [900, 930)
randy_busy = [
    (600, 630), 
    (900, 930)
]
add_busy_constraints(solver, randy_busy)

# Dylan's busy intervals (in minutes):
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 11:30  -> [660, 690)
# 12:30 to 13:00  -> [750, 780)
# 14:30 to 16:00  -> [870, 960)
dylan_busy = [
    (540, 630),
    (660, 690),
    (750, 780),
    (870, 960)
]
add_busy_constraints(solver, dylan_busy)

# Search for a valid meeting time:
# Given all constraints (especially start >= 960 and start + 60 <= 1020),
# the only feasible start time is 960.
if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
else:
    print("No valid meeting time could be found.")