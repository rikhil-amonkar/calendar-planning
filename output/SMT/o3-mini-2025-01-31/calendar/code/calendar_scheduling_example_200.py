from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: Monday from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int("start")

# The meeting must be scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # the meeting interval [start, start+duration) must either finish 
    # before busy_start or start after (or at) busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Stephen is free the entire day, so no constraints.

# Elijah's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 12:30 to 13:00 -> [750, 780)
# 14:30 to 15:00 -> [870, 900)
# 16:00 to 16:30 -> [960, 990)
elijah_busy = [(540, 570), (750, 780), (870, 900), (960, 990)]
add_busy_constraints(solver, elijah_busy)

# William's busy intervals:
# 9:30 to 10:00  -> [570, 600)
# 15:30 to 16:00 -> [930, 960)
william_busy = [(570, 600), (930, 960)]
add_busy_constraints(solver, william_busy)

# Jeremy's busy intervals:
# 9:00 to 9:30   -> [540, 570)
# 10:00 to 12:00 -> [600, 720)
# 13:00 to 15:00 -> [780, 900)
# 15:30 to 17:00 -> [930, 1020)
jeremy_busy = [(540, 570), (600, 720), (780, 900), (930, 1020)]
add_busy_constraints(solver, jeremy_busy)

# Timothy's busy intervals:
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 14:30 -> [690, 870)
# 15:30 to 16:00 -> [930, 960)
timothy_busy = [(600, 630), (690, 870), (930, 960)]
add_busy_constraints(solver, timothy_busy)

# Search for a valid start time.
solution_found = False
# The latest possible start time is 1020 - duration = 990.
for t in range(540, 991):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(sh, sm, eh, em))
        solution_found = True
        solver.pop()  # Restore state before exit.
        break
    solver.pop()  # Restore state and try next time slot.

if not solution_found:
    print("No valid meeting time could be found.")