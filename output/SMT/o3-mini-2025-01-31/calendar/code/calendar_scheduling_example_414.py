from z3 import Solver, Int, Or, sat

# Initialize the Z3 solver.
solver = Solver()

# Meeting parameters:
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")  # Meeting start time represented in minutes since midnight

# Constrain the meeting to be within the working day.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints that the meeting does not overlap a busy interval.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting [start, start+duration) must be fully before the busy interval,
        # or start after the busy interval.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Evelyn's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:00 to 12:30 -> [720, 750)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
evelyn_busy = [(540, 570), (720, 750), (870, 900), (930, 960)]
add_busy_constraints(solver, evelyn_busy)

# Kelly's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 15:30 to 17:00 -> [930, 1020)
kelly_busy = [(600, 630), (930, 1020)]
add_busy_constraints(solver, kelly_busy)

# Janice has no meetings.

# Marilyn has no meetings.

# Margaret's busy intervals:
# 9:00 to 9:30    -> [540, 570)
# 10:00 to 11:30  -> [600, 690)
# 12:00 to 13:30  -> [720, 810)
# 14:00 to 15:00  -> [840, 900)
# 16:30 to 17:00  -> [990, 1020)
margaret_busy = [(540, 570), (600, 690), (720, 810), (840, 900), (990, 1020)]
add_busy_constraints(solver, margaret_busy)

# Lauren's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 12:00 -> [660, 720)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 17:00 -> [960, 1020)
lauren_busy = [(570, 630), (660, 720), (750, 780), (870, 900), (960, 1020)]
add_busy_constraints(solver, lauren_busy)

# Henry's busy intervals:
# 9:30 to 10:30  -> [570, 630)
# 11:00 to 11:30 -> [660, 690)
# 12:00 to 13:00 -> [720, 780)
# 15:00 to 15:30 -> [900, 930)
# 16:00 to 17:00 -> [960, 1020)
henry_busy = [(570, 630), (660, 690), (720, 780), (900, 930), (960, 1020)]
add_busy_constraints(solver, henry_busy)

# Now search for a valid meeting start time by iterating through all possible candidates.
found = False
# Candidate meeting start times, in minutes, from 540 to 1020 - duration (inclusive)
for t in range(540, 1020 - duration + 1):
    solver.push()          # Save the current state
    solver.add(start == t) # Propose candidate start time t
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        found = True
        solver.pop()       # Restore state and break after a valid time is found.
        break
    solver.pop()           # Restore state for the next candidate

if not found:
    print("No valid meeting time could be found.")