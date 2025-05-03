from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 = 540 and 17:00 = 1020, meeting duration = 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure that the meeting is completely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints so that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # For each busy interval [bs, be), the meeting must finish before bs or start at or after be.
        solver.add(Or(start + duration <= bs, start >= be))

# Emma is free the entire day, so no constraints.

# Jonathan's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:30 to 11:00 -> [630, 660)
#   13:00 to 13:30 -> [780, 810)
#   15:30 to 16:00 -> [930, 960)
jonathan_busy = [(540, 570), (630, 660), (780, 810), (930, 960)]
add_busy_constraints(solver, jonathan_busy)

# George's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 10:30 -> [600, 630)
#   11:30 to 12:30 -> [690, 750)
#   15:00 to 15:30 -> [900, 930)
#   16:30 to 17:00 -> [990, 1020)
george_busy = [(540, 570), (600, 630), (690, 750), (900, 930), (990, 1020)]
add_busy_constraints(solver, george_busy)

# Stephen's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   10:00 to 11:00 -> [600, 660)
#   11:30 to 12:00 -> [690, 720)
#   12:30 to 13:00 -> [750, 780)
#   13:30 to 14:00 -> [810, 840)
#   15:00 to 17:00 -> [900, 1020)
stephen_busy = [(540, 570), (600, 660), (690, 720), (750, 780), (810, 840), (900, 1020)]
add_busy_constraints(solver, stephen_busy)

# Betty's busy intervals:
#   9:00 to 10:00   -> [540, 600)
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 12:30  -> [690, 750)
#   13:30 to 14:00  -> [810, 840)
#   15:00 to 16:00  -> [900, 960)
betty_busy = [(540, 600), (630, 660), (690, 750), (810, 840), (900, 960)]
add_busy_constraints(solver, betty_busy)

# Frank's busy intervals:
#   9:00 to 11:30   -> [540, 690)
#   12:00 to 14:30  -> [720, 870)
#   15:00 to 17:00  -> [900, 1020)
frank_busy = [(540, 690), (720, 870), (900, 1020)]
add_busy_constraints(solver, frank_busy)

# Search for the earliest valid meeting time by testing each possible start time minute by minute.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")