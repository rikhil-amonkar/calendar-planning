from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function: adds constraints ensuring the meeting doesn't conflict with busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting [start, start+duration) should finish before the busy interval starts OR start after it ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Judy's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 15:00 to 16:00 -> [900, 960)
judy_busy = [(540, 570), (660, 690), (720, 780), (900, 960)]
add_busy_constraints(solver, judy_busy)

# Alice's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 14:00 to 14:30 -> [840, 870)
alice_busy = [(660, 690), (840, 870)]
add_busy_constraints(solver, alice_busy)

# Christina's busy intervals:
# 9:30 to 10:00   -> [570, 600)
# 13:00 to 14:00  -> [780, 840)
# 14:30 to 16:00  -> [870, 960)
christina_busy = [(570, 600), (780, 840), (870, 960)]
add_busy_constraints(solver, christina_busy)

# Barbara's busy intervals:
# 13:30 to 14:30 -> [810, 870)
# 15:30 to 16:30 -> [930, 990)
barbara_busy = [(810, 870), (930, 990)]
add_busy_constraints(solver, barbara_busy)

# Sharon's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
# 16:30 to 17:00 -> [990, 1020)
sharon_busy = [(600, 630), (660, 690), (720, 810), (840, 870), (930, 960), (990, 1020)]
add_busy_constraints(solver, sharon_busy)

# Edward's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 13:30 -> [660, 810)
# 14:00 to 15:30 -> [840, 930)
edward_busy = [(540, 600), (660, 810), (840, 930)]
add_busy_constraints(solver, edward_busy)

# Sarah's busy intervals:
# 9:00 to 10:30  -> [540, 630)
# 11:00 to 13:00 -> [660, 780)
# 13:30 to 17:00 -> [810, 1020)
sarah_busy = [(540, 630), (660, 780), (810, 1020)]
add_busy_constraints(solver, sarah_busy)

# Try all possible start times within work hours to find a valid meeting slot.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(
            start_hr, start_min, end_hr, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")