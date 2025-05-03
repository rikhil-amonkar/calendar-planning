from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must finish before the busy interval begins,
        # or start after the busy interval ends:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Daniel's busy intervals:
# 9:30 to 10:00 -> [570, 600)
# 12:30 to 13:00 -> [750, 780)
daniel_busy = [(570, 600), (750, 780)]
add_busy_constraints(solver, daniel_busy)

# Wayne's busy intervals:
# 13:00 to 13:30 -> [780, 810)
# 14:00 to 14:30 -> [840, 870)
wayne_busy = [(780, 810), (840, 870)]
add_busy_constraints(solver, wayne_busy)

# Gloria's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:00 -> [690, 720)
gloria_busy = [(630, 660), (690, 720)]
add_busy_constraints(solver, gloria_busy)

# Stephanie's busy intervals:
# 9:30 to 15:30 -> [570, 930)
stephanie_busy = [(570, 930)]
add_busy_constraints(solver, stephanie_busy)

# Megan's busy intervals:
# 9:00 to 10:30 -> [540, 630)
# 11:00 to 14:00 -> [660, 840)
# 15:00 to 16:30 -> [900, 990)
megan_busy = [(540, 630), (660, 840), (900, 990)]
add_busy_constraints(solver, megan_busy)

# Since Stephanie is busy until 15:30 ([570,930)) and Megan is busy until 16:30 ([900,990)),
# the meeting must start at or after 990 (16:30) for both to be available.
# We now search for the earliest valid meeting starting time.
solution_found = False
for t in range(990, 1020 - duration + 1):  # starting from 990 (16:30)
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")