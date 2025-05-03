from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 60 minutes.
duration = 60
start = Int('start')
solver.add(start >= 540, start + duration <= 1020)

# Helper function: add constraints to ensure the meeting interval [start, start+duration)
# does not overlap a busy interval [bs, be)
def add_busy_constraints(solver, busy_intervals):
    for bs, be in busy_intervals:
        solver.add(Or(start + duration <= bs, start >= be))

# Aaron's busy intervals.
# 9:00 to 9:30 -> [540, 570)
# 10:30 to 11:00 -> [630, 660)
aaron_busy = [(540, 570), (630, 660)]
add_busy_constraints(solver, aaron_busy)

# Bryan's busy intervals.
# 9:00 to 9:30 -> [540, 570)
# 14:30 to 15:00 -> [870, 900)
bryan_busy = [(540, 570), (870, 900)]
add_busy_constraints(solver, bryan_busy)

# Philip's busy intervals.
# 9:00 to 9:30 -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 13:30 to 15:00 -> [810, 900)
# 15:30 to 17:00 -> [930, 1020)
philip_busy = [(540, 570), (600, 630), (810, 900), (930, 1020)]
add_busy_constraints(solver, philip_busy)

# Ronald's busy intervals.
# 9:00 to 9:30 -> [540, 570)
# 10:00 to 10:30 -> [600, 630)
# 11:30 to 12:00 -> [690, 720)
# 13:00 to 15:30 -> [780, 930)
ronald_busy = [(540, 570), (600, 630), (690, 720), (780, 930)]
add_busy_constraints(solver, ronald_busy)

# Try to find the earliest valid meeting start time.
solution_found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # save the current state
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".
              format(start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # restore state
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")