from z3 import *

# Create a Z3 solver instance.
solver = Solver()

# Define meeting parameters.
# Work hours: from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration: 30 minutes.
duration = 30
start = Int('start')

# Basic work hours constraint.
solver.add(start >= 540, start + duration <= 1020)

# Doris's preference: Avoid meetings after 12:30.
# To honor this, we require that the meeting finishes by 12:30 (750 minutes).
solver.add(start + duration <= 750)

# Helper function to add constraints ensuring the meeting interval [start, start+duration)
# does not overlap with a busy interval [busy_start, busy_end).
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Emma's busy intervals:
#   9:00 to 9:30   -> [540,570)
#  10:00 to 11:00  -> [600,660)
#  12:00 to 12:30  -> [720,750)
#  13:00 to 13:30  -> [780,810)
#  15:00 to 15:30  -> [900,930)
emma_busy = [(540,570), (600,660), (720,750), (780,810), (900,930)]
add_busy_constraints(solver, emma_busy)

# Ann is free the entire day (no busy intervals)

# Doris's busy intervals:
#  10:00 to 10:30 -> [600,630)
#  12:30 to 13:30 -> [750,810)
#  14:00 to 15:00 -> [840,900)
#  15:30 to 17:00 -> [930,1020)
doris_busy = [(600,630), (750,810), (840,900), (930,1020)]
add_busy_constraints(solver, doris_busy)

# Randy's busy intervals:
#   9:30 to 11:00  -> [570,660)
#  12:30 to 13:30  -> [750,810)
#  14:00 to 14:30  -> [840,870)
#  16:00 to 17:00  -> [960,1020)
randy_busy = [(570,660), (750,810), (840,870), (960,1020)]
add_busy_constraints(solver, randy_busy)

# Find the earliest valid meeting start time.
solution_found = False
# We must satisfy Doris's preference: start + duration <= 750.
# Hence, start can be at most 720. We search from 540 (09:00) to 720 (12:00).
for t in range(540, 721):
    solver.push()  # Save the current state.
    solver.add(start == t)
    if solver.check() == sat:
        model = solver.model()
        meeting_start = model[start].as_long()
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format.
        start_hr, start_min = divmod(meeting_start, 60)
        end_hr, end_min = divmod(meeting_end, 60)
        print("A valid meeting time is from {:02d}:{:02d} to {:02d}:{:02d}".format(start_hr, start_min, end_hr, end_min))
        solution_found = True
        solver.pop()  # Restore state.
        break
    solver.pop()

if not solution_found:
    print("No valid meeting time could be found.")