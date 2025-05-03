from z3 import Solver, Int, Or, sat

# Create a Z3 solver instance.
solver = Solver()

# Meeting parameters:
# Work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
duration = 30
start = Int("start")  # Meeting start time in minutes since midnight

# Constrain the meeting to be entirely within work hours.
solver.add(start >= 540, start + duration <= 1020)

# Helper function to add non-overlap constraints for given busy intervals.
def add_busy_constraints(solver, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Meeting [start, start+duration) doesn't overlap a busy period.
        solver.add(Or(start + duration <= busy_start, start >= busy_end))

# Participant: Russell
# Russell is free all day; no constraints are needed.

# Participant: Christina
# Busy during 12:00 to 12:30 -> [720, 750) and 16:00 to 16:30 -> [960, 990)
christina_busy = [(720, 750), (960, 990)]
add_busy_constraints(solver, christina_busy)

# Participant: Ethan
# Busy during 9:00 to 9:30 -> [540, 570) and 12:30 to 13:00 -> [750, 780)
ethan_busy = [(540, 570), (750, 780)]
add_busy_constraints(solver, ethan_busy)

# Participant: Brian
# Brian is free all day.

# Participant: Peter
# Busy during 9:00 to 12:00 -> [540, 720),
#           12:30 to 14:00 -> [750, 840),
#           15:00 to 15:30 -> [900, 930)
peter_busy = [(540, 720), (750, 840), (900, 930)]
add_busy_constraints(solver, peter_busy)

# Participant: Isabella
# Busy during 9:00 to 10:00 -> [540, 600),
#           10:30 to 14:30 -> [630, 870),
#           16:00 to 17:00 -> [960, 1020)
isabella_busy = [(540, 600), (630, 870), (960, 1020)]
add_busy_constraints(solver, isabella_busy)

# Participant: Dylan
# Busy during 9:30 to 11:30 -> [570, 690),
#           12:00 to 12:30 -> [720, 750),
#           13:30 to 14:00 -> [810, 840),
#           15:00 to 17:00 -> [900, 1020)
dylan_busy = [(570, 690), (720, 750), (810, 840), (900, 1020)]
add_busy_constraints(solver, dylan_busy)

# Search for the earliest available meeting time.
found = False
for t in range(540, 1020 - duration + 1):  # t ranges from 540 to 990 inclusive.
    solver.push()
    solver.add(start == t)
    if solver.check() == sat:
        meeting_start = t
        meeting_end = t + duration
        sh, sm = divmod(meeting_start, 60)
        eh, em = divmod(meeting_end, 60)
        print(f"A valid meeting time is from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}.")
        found = True
        solver.pop()
        break
    solver.pop()

if not found:
    print("No valid meeting time could be found.")