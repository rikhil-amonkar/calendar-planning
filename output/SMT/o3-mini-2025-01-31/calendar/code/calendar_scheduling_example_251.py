from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)
# Diana prefers to avoid meetings before 14:30.
# Therefore, the meeting should start no earlier than 14:30 (870 minutes).
solver.add(start >= 870)

# Helper function to add constraints ensuring that the meeting interval [start, start+duration)
# does not overlap with any given busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # The meeting must either end before a busy interval starts
        # or start after the busy interval ends.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Willie busy intervals:
# 10:00 to 11:30 -> [600, 690)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:30 -> [870, 930)
willie_busy = [(600, 690), (750, 780), (870, 930)]
add_busy_constraints(solver, willie_busy)

# Diana busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 12:00 to 12:30 -> [720, 750)
# 14:00 to 14:30 -> [840, 870)
# 15:00 to 15:30 -> [900, 930)
# 16:30 to 17:00 -> [990, 1020)
diana_busy = [(540, 570), (600, 630), (720, 750), (840, 870), (900, 930), (990, 1020)]
add_busy_constraints(solver, diana_busy)

# Olivia busy intervals:
# 9:00 to 9:30 -> [540, 570)
# 11:00 to 11:30 -> [660, 690)
olivia_busy = [(540, 570), (660, 690)]
add_busy_constraints(solver, olivia_busy)

# Kyle busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:00 -> [600, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
# 16:30 to 17:00 -> [990, 1020)
kyle_busy = [(540, 570), (600, 720), (750, 780), (870, 900), (990, 1020)]
add_busy_constraints(solver, kyle_busy)

# Kathleen busy intervals:
# 9:00 to 12:00   -> [540, 720)
# 12:30 to 13:00  -> [750, 780)
# 14:00 to 16:00  -> [840, 960)
# 16:30 to 17:00  -> [990, 1020)
kathleen_busy = [(540, 720), (750, 780), (840, 960), (990, 1020)]
add_busy_constraints(solver, kathleen_busy)

# We want to schedule the meeting at the earliest possible time.
solution_found = False
for t in range(870, 1020 - duration + 1):  # starting from 14:30 (870 minutes)
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