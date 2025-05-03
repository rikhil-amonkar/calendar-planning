from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters.
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30  # meeting duration in minutes
start = Int("start")  # meeting start time in minutes since midnight

# Ensure the meeting is scheduled within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add constraints for a participant's busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for b_start, b_end in busy_intervals:
        # The meeting [start, start+duration) must not overlap
        # with the busy interval [b_start, b_end).
        solver.add(Or(start + duration <= b_start, start >= b_end))

# Participant schedules:

# Roy's busy intervals:
# 11:00 to 11:30 -> [660, 690)
# 15:30 to 16:00 -> [930, 960)
roy_busy = [(660, 690), (930, 960)]
add_busy_constraints(solver, roy_busy)

# Kayla's busy intervals:
# 10:30 to 11:00 -> [630, 660)
# 12:00 to 13:00 -> [720, 780)
# 13:30 to 14:00 -> [810, 840)
# 14:30 to 15:00 -> [870, 900)
# 15:30 to 16:00 -> [930, 960)
kayla_busy = [(630, 660), (720, 780), (810, 840), (870, 900), (930, 960)]
add_busy_constraints(solver, kayla_busy)

# Alexis is free the entire day, so no constraints.

# Eugene's busy intervals:
# 11:30 to 12:00 -> [690, 720)
# 12:30 to 13:00 -> [750, 780)
eugene_busy = [(690, 720), (750, 780)]
add_busy_constraints(solver, eugene_busy)

# Matthew's busy intervals:
# 9:00 to 10:00   -> [540, 600)
# 11:00 to 12:30  -> [660, 750)
# 14:00 to 14:30  -> [840, 870)
# 15:00 to 16:00  -> [900, 960)
matthew_busy = [(540, 600), (660, 750), (840, 870), (900, 960)]
add_busy_constraints(solver, matthew_busy)

# Alice's busy intervals:
# 9:00 to 10:30   -> [540, 630)
# 11:00 to 13:00  -> [660, 780)
# 13:30 to 14:30  -> [810, 870)
# 15:00 to 16:30  -> [900, 990)
alice_busy = [(540, 630), (660, 780), (810, 870), (900, 990)]
add_busy_constraints(solver, alice_busy)

# Frank's busy intervals:
# 9:00 to 10:00    -> [540, 600)
# 11:30 to 12:00   -> [690, 720)
# 13:30 to 15:00   -> [810, 900)
# 15:30 to 16:00   -> [930, 960)
# 16:30 to 17:00   -> [990, 1020)
frank_busy = [(540, 600), (690, 720), (810, 900), (930, 960), (990, 1020)]
add_busy_constraints(solver, frank_busy)

# Search for the earliest valid meeting time.
found = False
for t in range(540, 1020 - duration + 1):
    solver.push()  # Save the current context.
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()  # Restore the context after a successful assignment.
        break
    solver.pop()  # Restore if the assignment didn't work.

if not found:
    print("No valid meeting time could be found.")