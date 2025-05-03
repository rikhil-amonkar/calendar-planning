from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define working hours in minutes: 9:00 (540) to 17:00 (1020)
# and the meeting duration of 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Ensure the meeting is completely within working hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that avoid busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        # Each busy interval [bs, be) must not overlap with the meeting.
        # So the meeting must end by the beginning of a busy interval, or start
        # at or after the end of the busy interval.
        solver.add(Or(start + duration <= bs, start >= be))

# Doris's busy intervals:
#   9:00 to 11:00   -> [540, 660)
#   13:30 to 14:00  -> [810, 840)
#   16:00 to 16:30  -> [960, 990)
doris_busy = [(540, 660), (810, 840), (960, 990)]
add_busy_constraints(solver, doris_busy)

# Theresa's busy intervals:
#   10:00 to 12:00  -> [600, 720)
theresa_busy = [(600, 720)]
add_busy_constraints(solver, theresa_busy)

# Christian is free the whole day; no constraints needed.

# Terry's busy intervals:
#   9:30 to 10:00   -> [570, 600)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:00  -> [750, 780)
#   13:30 to 14:00  -> [810, 840)
#   14:30 to 15:00  -> [870, 900)
#   15:30 to 17:00  -> [930, 1020)
terry_busy = [(570, 600), (690, 720), (750, 780), (810, 840), (870, 900), (930, 1020)]
add_busy_constraints(solver, terry_busy)

# Carolyn's busy intervals:
#   9:00 to 10:30   -> [540, 630)
#   11:00 to 11:30  -> [660, 690)
#   12:00 to 13:00  -> [720, 780)
#   13:30 to 14:30  -> [810, 870)
#   15:00 to 17:00  -> [900, 1020)
carolyn_busy = [(540, 630), (660, 690), (720, 780), (810, 870), (900, 1020)]
add_busy_constraints(solver, carolyn_busy)

# Kyle's busy intervals:
#   9:00 to 9:30   -> [540, 570)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:00  -> [750, 780)
#   14:30 to 17:00  -> [870, 1020)
kyle_busy = [(540, 570), (690, 720), (750, 780), (870, 1020)]
add_busy_constraints(solver, kyle_busy)

# Search for the earliest valid meeting time by checking each possible start time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()           # Save the current state.
    solver.add(start == t)  # Try a candidate start time.
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        start_hour, start_min = divmod(meeting_start, 60)
        end_hour, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hour, start_min, end_hour, end_min))
        found = True
        solver.pop()  # Restore the state.
        break
    solver.pop()      # Restore state if unsat for this t.
    
if not found:
    print("No valid meeting time could be found.")