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

# Helper function to add non-overlap constraints for a list of busy intervals.
def add_busy_constraints(solver, busy_intervals):
    # For each busy interval [busy_start, busy_end),
    # the meeting interval [start, start+duration) must either finish 
    # at or before busy_start or start at or after busy_end.
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Jonathan's busy intervals:
# 10:00 - 11:00 -> [600, 660)
# 15:00 - 15:30 -> [900, 930)
# 16:30 - 17:00 -> [990, 1020)
jonathan_busy = [(600, 660), (900, 930), (990, 1020)]
add_busy_constraints(solver, jonathan_busy)

# Lisa's busy intervals:
# 10:30 - 11:00 -> [630, 660)
# 11:30 - 12:00 -> [690, 720)
lisa_busy = [(630, 660), (690, 720)]
add_busy_constraints(solver, lisa_busy)

# Jerry's busy intervals:
# 9:00 - 13:00   -> [540, 780)
# 13:30 - 14:30  -> [810, 870)
# 15:00 - 17:00  -> [900, 1020)
jerry_busy = [(540, 780), (810, 870), (900, 1020)]
add_busy_constraints(solver, jerry_busy)

# Emma's busy intervals:
# 9:30 - 14:30   -> [570, 870)
# 15:00 - 17:00  -> [900, 1020)
emma_busy = [(570, 870), (900, 1020)]
add_busy_constraints(solver, emma_busy)

# Search for a valid start time.
solution_found = False
# The latest possible start time is 1020 - 30 = 990.
for t in range(540, 991):
    solver.push()
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
        solver.pop()
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")