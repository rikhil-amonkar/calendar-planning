from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540) to 17:00 (1020)
# But Jack prefers not to have meetings after 12:30 (750); 
# hence the meeting must finish by 12:30: start + duration <= 750.
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to be within work hours and Jack's preference.
solver.add(start >= 540, start + duration <= 1020)
solver.add(start + duration <= 750)  # meeting must finish by 12:30

# Helper function to add busy interval constraints.
def add_busy_constraints(solver, busy_intervals):
    for interval_start, interval_end in busy_intervals:
        # Ensure that the meeting [start, start+duration) does not overlap with the busy interval.
        solver.add(Or(start + duration <= interval_start, start >= interval_end))

# Jack's busy intervals (in minutes):
# 9:30 to 10:30 -> [570, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)  (but meeting can't reach this time due to preference)
# 14:00 to 14:30 -> [840, 870)
# 16:00 to 16:30 -> [960, 990)
jack_busy = [
    (570, 630),
    (660, 690),
    (750, 780),  # Not needed practically due to Jack's preference, but adding for completeness.
    (840, 870),
    (960, 990)
]
add_busy_constraints(solver, jack_busy)

# Charlotte's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 10:30 to 12:00 -> [630, 720)
# 12:30 to 13:30 -> [750, 810)
# 14:00 to 16:00 -> [840, 960)
charlotte_busy = [
    (570, 600),
    (630, 720),
    (750, 810),
    (840, 960)
]
add_busy_constraints(solver, charlotte_busy)

# Since Jack's preference forces the meeting to finish by 12:30 (750),
# the latest allowed start time is 720 (720+30=750).

# Now, iterate over possible meeting start times from 9:00 (540) to 12:00 (720).
found = False
for t in range(540, 720 + 1):
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