from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add busy interval constraints.
# For each busy interval [bs, be), the meeting must either finish before bs or start after be.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Jennifer's busy intervals:
#  - 10:30 to 11:00 -> [630, 660)
#  - 13:00 to 14:00 -> [780, 840)
#  - 16:30 to 17:00 -> [990, 1020)
jennifer_busy = [(630, 660), (780, 840), (990, 1020)]
add_busy_constraints(solver, jennifer_busy)

# Douglas's busy intervals:
#  - 9:00 to 9:30 -> [540, 570)
#  - 12:30 to 13:00 -> [750, 780)
douglas_busy = [(540, 570), (750, 780)]
add_busy_constraints(solver, douglas_busy)

# Lauren's busy intervals:
#  - 9:00 to 9:30 -> [540, 570)
#  - 10:00 to 10:30 -> [600, 630)
#  - 13:00 to 15:00 -> [780, 900)
lauren_busy = [(540, 570), (600, 630), (780, 900)]
add_busy_constraints(solver, lauren_busy)

# Daniel's busy intervals:
#  - 9:00 to 10:00   -> [540, 600)
#  - 10:30 to 11:00  -> [630, 660)
#  - 11:30 to 12:30  -> [690, 750)
#  - 13:00 to 14:30  -> [780, 870)
#  - 15:30 to 16:30  -> [930, 990)
daniel_busy = [(540, 600), (630, 660), (690, 750), (780, 870), (930, 990)]
add_busy_constraints(solver, daniel_busy)

# Abigail's busy intervals:
#  - 9:30 to 10:30 -> [570, 630)
#  - 11:30 to 12:00 -> [690, 720)
#  - 12:30 to 14:30 -> [750, 870)
#  - 15:30 to 16:00 -> [930, 960)
abigail_busy = [(570, 630), (690, 720), (750, 870), (930, 960)]
add_busy_constraints(solver, abigail_busy)

# Catherine's busy intervals:
#  - 9:00 to 11:00   -> [540, 660)
#  - 11:30 to 14:00  -> [690, 840)
#  - 14:30 to 15:30  -> [870, 930)
#  - 16:30 to 17:00  -> [990, 1020)
catherine_busy = [(540, 660), (690, 840), (870, 930), (990, 1020)]
add_busy_constraints(solver, catherine_busy)

# Try to find the earliest meeting time that satisfies all constraints.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()
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