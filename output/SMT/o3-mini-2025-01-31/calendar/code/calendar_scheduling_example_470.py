from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Represents the meeting start time in minutes from midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Carol would rather not meet on Monday after 10:00.
# To honor Carol's preference, we force the meeting to finish by 10:00 (600 minutes).
solver.add(start + duration <= 600)

# Helper function to add constraints that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bstart, bend in busy_intervals:
        # The meeting [start, start+duration) must either finish before the busy interval starts
        # or begin after the busy interval ends.
        solver.add(Or(start + duration <= bstart, start >= bend))

# Participant schedules (times in minutes from midnight):

# Jordan's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
# 12:30 to 13:00 -> [750, 780)
# 13:30 to 14:00 -> [810, 840)
jordan_busy = [(540, 570), (660, 690), (750, 780), (810, 840)]
add_busy_constraints(solver, jordan_busy)

# Madison's busy intervals:
# 10:00 to 11:00 -> [600, 660)
# 11:30 to 12:00 -> [690, 720)
# 14:30 to 15:30 -> [870, 930)
# 16:30 to 17:00 -> [990, 1020)
madison_busy = [(600, 660), (690, 720), (870, 930), (990, 1020)]
add_busy_constraints(solver, madison_busy)

# Kimberly's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 16:30 to 17:00 -> [990, 1020)
kimberly_busy = [(690, 720), (990, 1020)]
add_busy_constraints(solver, kimberly_busy)

# Carol's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 10:30 to 12:00 -> [630, 720)
# 13:30 to 14:00 -> [810, 840)
# 16:00 to 16:30 -> [960, 990)
carol_busy = [(540, 570), (630, 720), (810, 840), (960, 990)]
add_busy_constraints(solver, carol_busy)
# (Plus Carol's preference already added above: meeting must finish by 600)

# Nathan's busy intervals:
# 10:00 to 14:00 -> [600, 840)
# 14:30 to 15:30 -> [870, 930)
# 16:00 to 17:00 -> [960, 1020)
nathan_busy = [(600, 840), (870, 930), (960, 1020)]
add_busy_constraints(solver, nathan_busy)

# Walter's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 12:30 -> [720, 750)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 16:00 -> [870, 960)
walter_busy = [(540, 570), (600, 630), (660, 690), (720, 750), (810, 840), (870, 960)]
add_busy_constraints(solver, walter_busy)

# Aaron's busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:00 to 12:00 -> [660, 720)
# 13:30 to 14:00 -> [810, 840)
# 15:30 to 17:00 -> [930, 1020)
aaron_busy = [(540, 570), (600, 630), (660, 720), (810, 840), (930, 1020)]
add_busy_constraints(solver, aaron_busy)

# Since Carol prefers not to meet after 10:00, with the meeting lasting 30 minutes,
# the only possible start times are such that start + 30 <= 600. That is, start <= 570.
# We now search for the earliest meeting time satisfying all constraints.
found = False
for t in range(540, 571):  # 540 to 570 inclusive are potential start times.
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