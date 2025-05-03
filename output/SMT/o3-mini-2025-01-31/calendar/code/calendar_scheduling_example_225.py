from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes.
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight.

# Constrain the meeting to occur within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Additional constraint: Doris cannot meet before 15:00 (900 minutes).
solver.add(start >= 900)

# Helper function: for each busy interval (busy_start, busy_end),
# add the constraint that the meeting [start, start+duration) does not overlap it.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jean's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 11:30 to 12:30 -> [690, 750)
# 14:00 to 15:00 -> [840, 900)
# 16:00 to 16:30 -> [960, 990)
jean_busy = [(630, 660), (690, 750), (840, 900), (960, 990)]
add_busy_constraints(solver, jean_busy)

# Terry has no meetings (free the entire day).

# Amber has no meetings.

# Doris's busy intervals:
# 10:00 to 11:30 -> [600, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:00 to 14:30 -> [840, 870)
# 15:30 to 16:00 -> [930, 960)
doris_busy = [(600, 690), (720, 810), (840, 870), (930, 960)]
add_busy_constraints(solver, doris_busy)

# Joan's busy intervals:
# 9:00 to 11:30  -> [540, 690)
# 12:00 to 13:30 -> [720, 810)
# 14:30 to 16:30 -> [870, 990)
joan_busy = [(540, 690), (720, 810), (870, 990)]
add_busy_constraints(solver, joan_busy)

# We now search for the earliest valid meeting time.
solution_found = False
# Latest valid start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save the current state
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        # Convert minutes into HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")